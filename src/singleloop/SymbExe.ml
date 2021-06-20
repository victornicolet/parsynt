(**
   This file is part of Parsynt.

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
*)

open Beta
open Expressions
open FError
open Fn
open Format
open Utils

let debug = ref false

let verbose = ref false

type exec_info = {
  context : context;
  state_exprs : fnExpr IM.t;
  intermediate_states : fnExpr list IM.t;
  index_exprs : fnExpr IM.t;
  inputs : ES.t;
}
(**
   Structure with the informatino needed during the symbolic execution:
   - context contains variables information (intpurs, state variables)
   - state exprs maps state variable ids to expressions.
   - index exprs maps index variable ids to expressions.
   - inputs is the set of input expressions.
*)

exception SymbExeError of string * fnExpr

let print_SymbExeError (exc : exn) : string option =
  match exc with
  | SymbExeError (s, e) ->
      fprintf str_formatter "@[<v 4>[SYMBOLIC EXECUTION ERROR] %s.@;%a@]" s FnPretty.pp_fnexpr e;
      Some (flush_str_formatter ())
  | _ -> None

;;
Printexc.register_printer print_SymbExeError

(* Array size must be bounded during the symbolic execution. *)

(** Create a mapping from variable ids to variable expressions to start the
    algorithm *)
let var_to_symbols = IH.create 10

let symbols_to_vars = IH.create 10

let _clear_symbols () =
  Base.Hashtbl.clear var_to_symbols;
  Base.Hashtbl.clear symbols_to_vars

let add_symbol orig_vi =
  let var = mkFnVar ("init_" ^ orig_vi.vname) orig_vi.vtype in
  IH.add var_to_symbols orig_vi.vid var;
  IH.add symbols_to_vars var.vid orig_vi;
  var

let replace_symbols_by_vars expr =
  let rec r_vars v =
    match v with
    | FnVariable var ->
        if IH.mem symbols_to_vars var.vid then FnVariable (IH.find symbols_to_vars var.vid)
        else FnVariable var
    | FnArray (a, e) -> FnArray (r_vars a, r_symbols e)
  and r_symbols e =
    transform_expr2
      { case = (fun _ -> false); on_case = (fun _ e -> e); on_var = r_vars; on_const = identity }
      e
  in
  r_symbols expr

let replace_vars_by_symbols expr =
  let rec replace_vars v =
    match v with
    | FnVariable var ->
        if IH.mem var_to_symbols var.vid then FnVariable (IH.find var_to_symbols var.vid)
        else FnVariable var
    | FnArray (a, e) -> FnArray (replace_vars a, replace_symbols e)
  and replace_symbols e =
    transform_expr2
      {
        case = (fun _ -> false);
        on_case = (fun _ e -> e);
        on_var = replace_vars;
        on_const = identity;
      }
      e
  in
  replace_symbols expr

let create_symbol_map vs =
  VarSet.fold
    (fun vi map ->
      let eqvi = add_symbol vi in
      IM.set vi.vid
        (if is_matrix_type vi.vtype then
         FnVector
           (ListTools.init Dimensions._SYMBEX_FINITE_ (fun i ->
                FnVector
                  (ListTools.init Dimensions._SYMBEX_FINITE_ (fun j ->
                       FnVar
                         (FnArray (FnArray (FnVariable eqvi, FnConst (CInt i)), FnConst (CInt j)))))))
        else if is_array_type vi.vtype then
          FnVector
            (ListTools.init Dimensions._SYMBEX_FINITE_ (fun i ->
                 FnVar (FnArray (FnVariable eqvi, FnConst (CInt i)))))
        else FnVar (FnVariable eqvi))
        map)
    vs IM.empty

let _pe s e = Format.printf "{%s} %a@." s FnPretty.cp_fnexpr e

(* ----------------------------------------------------------------------  *)
(* Partial interpretation: produces simplified expression. *)

let rec partial_interpret e =
  let symb_inter e =
    match e with
    | FnBinop (op, e1, e2) -> (
        let maybe_int_op =
          match op with
          | Plus -> Some (fun a b -> a + b)
          | Minus -> Some (fun a b -> a - b)
          | Times -> Some (fun a b -> a * b)
          | Div -> Some (fun a b -> a / b)
          | _ -> None
        in
        let maybe_bool_op =
          match op with
          | And -> Some (fun a b -> a && b)
          | Or -> Some (fun a b -> a && b)
          | Xor -> Some (fun a b -> (a && b) || ((not a) && not b))
          | _ -> None
        in
        match (e1, e2) with
        | FnConst (CInt i1), FnConst (CInt i2) -> (
            match maybe_int_op with
            | Some fop -> FnConst (CInt (fop i1 i2))
            | None -> fail_type_error "Expected int.")
        | FnConst (CBool b1), FnConst (CBool b2) -> (
            match maybe_bool_op with
            | Some fop -> FnConst (CBool (fop b1 b2))
            | None -> fail_type_error "Expected bool.")
        | e', FnConst (CInt i1) -> (
            match (op, i1) with
            | Plus, 0 -> e'
            | Minus, 0 -> e'
            | Times, 1 -> e'
            | Times, 0 -> FnConst (CInt 0)
            | Div, 1 -> e'
            | Div, 0 -> fail_type_error "Division by zero."
            | _ -> FnBinop (op, e', FnConst (CInt i1)))
        | FnConst (CInt i0), e' -> (
            match (i0, op) with
            | 0, Plus -> e'
            | 0, Minus -> FnUnop (Neg, e')
            | 1, Times -> e'
            | 0, Times -> FnConst (CInt 0)
            | 1, Div -> e
            | 0, Div -> FnConst (CInt 0)
            | _ -> FnBinop (op, FnConst (CInt i0), e'))
        | e', FnConst (CBool b) | FnConst (CBool b), e' -> (
            match (op, b) with
            | And, true -> e'
            | Or, true -> FnConst (CBool true)
            | And, false -> FnConst (CBool false)
            | Or, false -> e'
            | _ -> e)
        | _ -> e)
    | FnUnop (op, e1) -> (
        match (op, e1) with
        | Neg, FnConst (CInt i1) -> FnConst (CInt (-i1))
        | Not, FnConst (CBool b) -> FnConst (CBool (not b))
        | Abs, FnConst (CInt i1) -> FnConst (CInt (abs i1))
        | Add1, FnConst (CInt i1) -> FnConst (CInt (i1 + 1))
        | Sub1, FnConst (CInt i1) -> FnConst (CInt (i1 - 1))
        | _ -> e)
    | FnCond (c, e1, e2) -> (
        match partial_interpret c with
        | FnConst (CBool true) -> e1
        | FnConst (CBool false) -> e2
        | _ -> e)
    | _ -> e
  in
  peval (symb_inter e)

(* --------------------------------------------------------------------------*)
(* Intermediary functions for unfold_once *)

let _intermediate_states : fnExpr list ref = ref []

let saved_intermediate_state = ref []

let clear_intermediate_states () = _intermediate_states := []

let add_intermediate_state (i : int) (state : fnExpr) : unit =
  match state with
  | FnRecord (_, _) ->
      if List.length !_intermediate_states = i then
        _intermediate_states := !_intermediate_states @ [ state ]
      else (
        printf "[ERROR] Intermediate states =@;%a,@.i =@;%i,@.state =@;%a@." FnPretty.cp_expr_list
          !_intermediate_states i FnPretty.cp_fnexpr state;
        raise (SymbExeError ("wrong number of states", state)))
  | _ -> raise (SymbExeError ("Cannot add a state that is not a record.", state))

let save_intermediate_states () =
  saved_intermediate_state := !_intermediate_states;
  _intermediate_states := []

let get_one_intermediate_val (var : fnV) : fnExpr list =
  let some_vals =
    List.mapi
      (fun _ e ->
        match e with
        | FnRecord (vs, emap) -> (
            assert (VarSet.cardinal vs = IM.cardinal emap);
            try Some (IM.find var.vid emap) with Not_found -> None)
        | _ -> None)
      !_intermediate_states
  in
  List.map check_option (List.filter is_some some_vals)

let get_intermediate_values (varset : VarSet.t) : fnExpr list IM.t =
  VarSet.fold
    (fun var imap ->
      let ivals = get_one_intermediate_val var in
      IM.set var.vid ivals imap)
    varset IM.empty

type ex_env = {
  ebound : VarSet.t;
  eindex : VarSet.t;
  ebexprs : fnExpr IM.t;
  eiexprs : fnExpr IM.t;
  ereads : ES.t;
}

let _pp_env fmt env =
  Format.fprintf fmt "@[Bound: %a.@;Exprs: %a@;Indexes: %a@;Exprs: %a@;Reads: %a@]@." VarSet.pp_vs
    env.ebound FnPretty.cp_expr_map env.ebexprs VarSet.pp_vs env.eindex FnPretty.cp_expr_map
    env.eiexprs
    (FnPretty.pp_expr_set ~sep:(fun fmt () -> Format.fprintf fmt "@;"))
    env.ereads

let add_read_env env e = { env with ereads = ES.add e env.ereads }

let up_join eenv1 eenv2 = { eenv1 with ereads = ES.union eenv1.ereads eenv2.ereads }

let update_indexval env ivar i_intval =
  { env with eiexprs = IM.set ivar.vid (FnConst (CInt i_intval)) env.eiexprs }

let update_binding ?(offset = -1) v e env =
  if offset > -1 then
    let vec =
      try IM.find v.vid env.ebexprs
      with Not_found -> raise (SymbExeError ("update_binding : Unbound array var.", e))
    in
    match vec with
    | FnVector ea ->
        let ea' = ListTools.replace_ith ea offset e in
        { env with ebexprs = IM.set v.vid (FnVector ea') env.ebexprs }
    | _ -> raise (SymbExeError ("update_binding: Array var type, not vector expression.", vec))
  else { env with ebound = VarSet.add v env.ebound; ebexprs = IM.set v.vid e env.ebexprs }

(* Parallel bindings *)
let rec do_bindings (sin : ex_env) (bindings : (fnLVar * fnExpr) list) : fnExpr * ex_env =
  let out_env =
    List.fold_left (fun uenv (var, expr) -> do_binding sin uenv (var, expr)) sin bindings
  in
  (FnRecord (VarSet.empty, IM.empty), out_env)

and do_binding sin uenv (var, expr) : ex_env =
  let e, reads = do_expr sin expr in
  match var with
  | FnVariable v -> up_join (update_binding v e uenv) reads
  | FnArray (FnVariable a, i) ->
      let i', _ = do_expr sin i in
      up_join (update_binding ~offset:(concrete_index i') a e uenv) reads
  | FnArray _ -> raise (SymbExeError ("do_binding: Setting 2D Array cell not supported.", expr))

and do_expr env expr : fnExpr * ex_env =
  match expr with
  | FnVar v -> do_var env v
  | FnConst _ -> (expr, env)
  | FnLetIn (bindings, body) ->
      let _, s' = do_bindings env bindings in
      do_expr s' body
  | FnRec (igu, (vs, bs), (s, body)) -> do_loop env igu (vs, bs) (s, body)
  | FnBinop (op, e1, e2) ->
      let e1', s1 = do_expr env e1 in
      let e2', s2 = do_expr env e2 in
      (partial_interpret (FnBinop (op, e1', e2')), up_join s1 s2)
  | FnUnop (op, e) ->
      let e', s' = do_expr env e in
      (partial_interpret (FnUnop (op, e')), s')
  | FnCond (c, et, ef) ->
      let c', sc' = do_expr env c in
      let et', set' = do_expr env et in
      let ef', sef' = do_expr env ef in
      (partial_interpret (FnCond (c', et', ef')), up_join sc' (up_join set' sef'))
  | FnArraySet (a, i, e) ->
      let a', sa' = do_expr env a in
      let i', si' = do_expr env i in
      let e', se' = do_expr env e in
      let sf = up_join sa' (up_join si' se') in
      let e'' = partial_interpret e' in
      (do_set_array sin a' i' e'', sf)
  | FnRecordMember (re, s) ->
      let re', env' = do_expr env re in
      let e', env' =
        match re' with
        | FnRecord (vs, emap) ->
            let e'' = IM.find (VarSet.find_by_name vs s).vid emap in
            do_expr env' e''
        | _ ->
            if !verbose then printf "[ERROR] %a@." FnPretty.pp_fnexpr (FnRecordMember (re', s));
            raise
              (SymbExeError
                 ("do_expr (FnRecordMember): Expected a record in record member accessor.", re'))
      in
      (e', env')
  | FnRecord (vs, emap) ->
      let emap' = IM.map (do_expr env) emap in
      let _, esl' = Base.List.unzip (IM.to_alist emap') in
      let el', sl' = Base.List.unzip esl' in
      let typecheck = VarSet.cardinal vs = List.length el' in
      if typecheck then
        (FnRecord (vs, IM.map fst emap'), List.fold_left (fun sf s' -> up_join sf s') env sl')
      else raise (TypeCheckError (record_type vs, type_of expr, expr))
  | FnVector el ->
      let el', sl' = Base.List.unzip (List.map (do_expr env) el) in
      ( FnVector (List.map partial_interpret el'),
        List.fold_left (fun sf s' -> up_join sf s') env sl' )
  | FnApp (_, _, _) -> (expr, env)
  | FnChoice el ->
      let el', sl' = Base.List.unzip (List.map (do_expr env) el) in
      ( FnChoice (List.map partial_interpret el'),
        List.fold_left (fun sf s' -> up_join sf s') env sl' )
  | FnHoleL (ht, v, cs, e, d) ->
      let e', s' = do_expr env e in
      (FnHoleL (ht, v, cs, e', d), s')
  | FnHoleR (ht, cs, e, d) ->
      let e', s' = do_expr env e in
      (FnHoleR (ht, cs, e', d), s')
  | _ ->
      if !verbose then
        Format.printf "[ERROR] do_expr not implemented for %a" FnPretty.pp_fnexpr expr;
      raise (SymbExeError ("do_expr: Match case not implemented.", expr))

and do_set_array _ a i e : fnExpr =
  try
    match a with
    | FnVector e_ar -> FnVector (ListTools.replace_ith e_ar (concrete_index i) e)
    | _ ->
        raise (SymbExeError ("do_set_array: Cannot modify an expression that is not a vector.", e))
  with exc ->
    if !debug then
      Format.printf "[ERROR] Cannot set array: %a[%a] = %a" FnPretty.pp_fnexpr a FnPretty.pp_fnexpr
        i FnPretty.pp_fnexpr e;
    raise exc

and concrete_index i =
  match i with
  | FnConst (CInt i') -> i'
  | FnConst (CInt64 i') -> Int64.to_int i'
  | _ ->
      if !verbose then Format.printf "[ERROR] %a is not concrete." FnPretty.pp_fnexpr i;
      raise
        (SymbExeError
           ("concrete_index: Cannot use non-concretized indexes in symbolic execution.", i))

and do_var env v : fnExpr * ex_env =
  match v with
  | FnVariable vi ->
      (* It is a state variables - or a variable bound in the environment. *)
      if IM.mem vi.vid env.ebexprs then (IM.find vi.vid env.ebexprs, env)
        (* It is an index variable,, also bound in the environment. *)
      else if IM.mem vi.vid env.eiexprs then (IM.find vi.vid env.eiexprs, env)
        (* It is an input, that is never bound or modified *)
      else if is_array_type (type_of_var v) then (FnVar v, env)
      else (FnVar v, add_read_env env (FnVar v))
  | FnArray (a, i) -> (
      let a', _ = do_var env a in
      let i', env'' = do_expr env i in
      (* The array accessed can be:
         - still a variable if it is an input.
         - the expression form the env if it is a state variable. In this case
         it has to be a FnVector. *)
      match a' with
      | FnVar av ->
          let e = FnVar (FnArray (av, i')) in
          (e, add_read_env env e)
      | FnVector ar -> (
          let i0 = concrete_index i' in
          try (List.nth ar i0, env'')
          with _ ->
            raise (SymbExeError ("In vector, cannot access cell " ^ string_of_int i0, FnVector ar)))
      | _ ->
          if !verbose then
            printf "[ERROR] Received %a instead of input variable or vector.@." FnPretty.cp_fnexpr
              a';
          raise (SymbExeError ("do_var : An array variable should be an input or a vector.", a')))

and do_loop (env : ex_env) (init, g, u) (_, bs) (s, body) : fnExpr * ex_env =
  let indexvar = VarSet.max_elt (used_in_fnexpr u) in
  let static = Dimensions._SYMBEX_FINITE_ - 1 in
  let i0 =
    match peval (Dimensions.concretize init) with
    | FnConst (CInt c) -> c
    | FnConst (CInt64 c64) -> Int64.to_int c64
    | _ -> 0
  in

  let c_stop0 =
    match Dimensions.concretize g with
    | FnBinop (Lt, _, FnConst (CInt c)) | FnBinop (Gt, FnConst (CInt c), _) -> fun i -> i >= c
    | FnBinop (Le, _, FnConst (CInt c)) | FnBinop (Ge, FnConst (CInt c), _) -> fun i -> i > c
    | FnBinop (Lt, FnConst (CInt c), _) | FnBinop (Gt, _, FnConst (CInt c)) -> fun i -> i <= c
    | FnBinop (Le, FnConst (CInt c), _) | FnBinop (Ge, _, FnConst (CInt c)) -> fun i -> i < c
    | _ -> fun i -> i >= static
  in

  let c_update, c_stop =
    match u with
    | FnBinop (Plus, _, _) | FnUnop (Add1, _) ->
        if !verbose then printf "[INFO] Rightwards loop.@.";
        ((fun i -> i + 1), fun i -> c_stop0 i || i >= 5)
    | FnBinop (Minus, _, _) | FnUnop (Sub1, _) ->
        if !verbose then printf "[INFO] Leftwards loop.@.";
        ((fun i -> i - 1), fun i -> c_stop0 i || i <= 0)
    | _ ->
        if !verbose then printf "[INFO] Rightwards loop.@.";
        ((fun i -> i + 1), fun i -> c_stop0 i || i >= 5)
  in

  let exec_loop k out_env body =
    let rec aux k counter env body =
      if c_stop k then (
        let record = IM.find s.vid env.ebexprs in
        add_intermediate_state (counter + 1) record;
        (record, env))
      else
        let res, _ = do_expr (update_indexval env indexvar k) body in
        add_intermediate_state (counter + 1) res;
        aux (c_update k) (counter + 1)
          { env with ebound = VarSet.singleton s; ebexprs = IM.singleton s.vid res }
          body
    in
    let start_env =
      let bs', _ = do_expr env bs in
      add_intermediate_state 0 bs';
      { out_env with ebound = VarSet.singleton s; ebexprs = IM.singleton s.vid bs' }
    in
    let res_final, env_final = aux k 0 start_env body in
    save_intermediate_states ();
    (res_final, env_final)
  in
  exec_loop i0 env body

let filter_state einfo em = IM.filter (fun k _ -> VarSet.has_vid einfo.context.state_vars k) em

let env_from_exec_info (einfo : exec_info) : ex_env =
  {
    ebound = einfo.context.state_vars;
    eindex = einfo.context.index_vars;
    ebexprs = IM.map replace_vars_by_symbols (filter_state einfo einfo.state_exprs);
    eiexprs = IM.map replace_vars_by_symbols einfo.index_exprs;
    ereads = einfo.inputs;
  }

let unfold (exec_info : exec_info) (func : fnExpr) : fnExpr IM.t * ES.t =
  clear_intermediate_states ();
  let env' = env_from_exec_info exec_info in
  let r, env'' = do_expr env' func in
  let env_final =
    match r with
    | FnRecord (_, emap) -> { env'' with ebexprs = IM.update_all env''.ebexprs emap }
    | _ -> env''
  in
  _intermediate_states := List.map replace_symbols_by_vars !_intermediate_states;
  ( (filter_state exec_info --> IM.map replace_symbols_by_vars) env_final.ebexprs,
    es_transform replace_symbols_by_vars env_final.ereads )

let unfold_expr (exec_info : exec_info) (e : fnExpr) : fnExpr * ES.t =
  clear_intermediate_states ();
  let e', env' = do_expr (env_from_exec_info exec_info) e in
  _intermediate_states := List.map replace_symbols_by_vars !_intermediate_states;
  (replace_symbols_by_vars e', es_transform replace_symbols_by_vars env'.ereads)

(** unfold_once : simulate the applciation of a function body to a set of
    expressions for the state variables. The inputs are replaced by fresh
    variables.
    @raise {e Not_found} if an elemt is missing at some stage of the
    algorithm.

    @param stv the state variable of the function, they have to have the same
    ids as the variables present in the input expressions.
    @param exprs the inital expressions of the state variable before applying
    the function.
    @param func the function that we want to apply to the expressions.
    @param index_expr the index is a special expression not appearing in the
    state nor in the expressions so we have to add it to avoid creating false
    read-only input symbols.

    @return a map of variable ids in the state to the expressions resulting from
    the application of the function to the input variables expressions.
*)
let unfold_once ?(silent = false) exec_info inp_func =
  let _ = silent in
  let new_exprs, inputs = unfold exec_info inp_func in
  {
    exec_info with
    state_exprs = new_exprs;
    intermediate_states = get_intermediate_values exec_info.context.state_vars;
    inputs;
  }
