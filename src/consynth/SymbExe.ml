(**
   This file is part of Parsynt.

    Foobar is free software: you can redistribute it and/or modify
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
open Utils
open FError
open Expressions
open FuncTypes


let debug = ref false

(**
   Structure with the informatino needed during the symbolic execution:
   - context contains variables information (intpurs, state variables)
   - state exprs maps state variable ids to expressions.
   - index exprs maps index variable ids to expressions.
   - inputs is the set of input expressions.
*)
type exec_info =
  { context : context;
    state_exprs : fnExpr IM.t;
    index_exprs : fnExpr IM.t;
    inputs : ES.t  }

(* Array size must be bounded during the symbolic execution. *)
let _MAX_ARRAY_SIZE_ = Conf.get_conf_int "symbolic_execution_finitization"

let _arsize_ = ref _MAX_ARRAY_SIZE_
(** Create a mapping from variable ids to variable expressions to start the
    algorithm *)
let create_symbol_map vs=
  VarSet.fold
    (fun vi map ->
              IM.add vi.vid
                (if is_array_type vi.vtype then
                   (FnVector (Array.init !_arsize_
                                (fun i -> FnVar(FnArray(FnVariable vi, FnConst (CInt i))))))
                 else
                   (FnVar (FnVariable vi)))
                map) vs IM.empty



(** ----------------------------------------------------------------------  *)
(** Partial interpretation: produces simplified expression. *)

let rec partial_interpret e =
  match e with
  | FnBinop(op, e1, e2) ->
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
      | Xor -> Some (fun a b -> (a && b) || ((not a) && (not b)))
      | _ -> None
    in
    (match e1, e2 with
    | FnConst (CInt i1), FnConst (CInt i2) ->
      (match maybe_int_op with
       | Some fop -> FnConst (CInt (fop i1 i2))
       | None -> fail_type_error "Expected int.")

    | FnConst (CBool b1), FnConst (CBool b2) ->
      (match maybe_bool_op with
       | Some fop -> FnConst (CBool (fop b1 b2))
       | None -> fail_type_error "Expected bool.")

    | e', FnConst (CInt i1) ->
      (match op, i1 with
       | Plus, 0 -> e'
       | Minus, 0 -> e'
       | Times, 1 -> e'
       | Times, 0 -> FnConst (CInt 0)
       | Div, 1 -> e'
       | Div, 0 -> fail_type_error "Division by zero."
       | _ -> FnBinop (op, e', FnConst (CInt i1)))

    | FnConst (CInt i0), e' ->
      (match i0, op with
       | 0, Plus -> e'
       | 0, Minus -> FnUnop(Neg, e')
       | 1, Times -> e'
       | 0, Times -> FnConst (CInt 0)
       | 1, Div -> e
       | 0, Div -> FnConst (CInt 0)
       | _ -> FnBinop (op, FnConst (CInt i0), e'))

    | e', FnConst (CBool b)
    | FnConst (CBool b), e' ->
      (match op, b with
       | And, true -> e'
       | Or, true -> FnConst (CBool true)
       | And, false -> FnConst (CBool false)
       | Or, false -> e'
       | _ -> e)

    | _ -> e)


  | FnUnop (op, e1) ->
    (match op, e1 with
     | Neg, FnConst (CInt i1) -> FnConst (CInt (- i1))
     | Not, FnConst (CBool b) -> FnConst (CBool (not b))
     | Abs, FnConst (CInt i1) -> FnConst (CInt (abs i1))
     | Add1, FnConst (CInt i1) -> FnConst (CInt (i1 + 1))
     | Sub1, FnConst (CInt i1) -> FnConst (CInt (i1 - 1))
     | _ -> e)


  | FnCond(c, e1, e2) ->
    (match partial_interpret c with
    | FnConst (CBool true) -> e1
    | FnConst (CBool false) -> e2
    | _ -> e)


  | _ -> e


(** --------------------------------------------------------------------------*)
(** Intermediary functions for unfold_once *)
let rec unfold new_exprs exec_info func =

  let rec apply_let_exprs new_exprs (let_list : (fnLVar * fnExpr) list) exec_info =
    List.fold_left
      update_expressions (new_exprs, exec_info.inputs) let_list

  and update_expressions (new_exprs, read_exprs) (var, expr) =
    match var with
    | FnVariable vi ->
      let vid = vi.vid in
      let nexpr, n_rexprs = unfold_expr exec_info expr in
      if !debug then
        (Format.fprintf Format.std_formatter "Set of read exprs : %a@."
           (fun fmt a -> FPretty.pp_expr_set fmt a)
           (ES.union n_rexprs read_exprs))
      else
        ();
      IM.add vid nexpr new_exprs, ES.union n_rexprs read_exprs

    | FnArray (v, e) ->
      begin
        match v, e with
        | FnVariable a_vi, FnConst (CInt i) ->
          let vid = a_vi.vid in
          let avect =
            try
              match IM.find vid exec_info.state_exprs with
              | FnVector av -> av
              | _ -> failhere __FILE__ "update_expressions"
                       "Expected a vector expression in the state of array variable."
            with Not_found ->
              failhere __FILE__ "update_expressions"
                (Format.sprintf "Couldn't find an expression for array %s." a_vi.vname)
          in
          let nexpr_i , n_rexprs = unfold_expr ~loc:i exec_info expr in
          Array.set avect i nexpr_i;
          IM.add vid (FnVector avect) new_exprs, ES.union n_rexprs read_exprs
        | _ ->
          exception_on_expression "Unspported array access in unfold" (FnVar var)
      end
  in
  match func with
  | FnLetExpr let_list ->
    apply_let_exprs new_exprs let_list exec_info
  | FnLetIn (let_list, let_cont) ->
    let new_exprs, new_reads = apply_let_exprs new_exprs let_list exec_info in
    unfold new_exprs
      {exec_info with
       state_exprs = IM.update_all exec_info.state_exprs new_exprs;
       inputs = ES.union new_reads exec_info.inputs} let_cont
  | _ -> failhere __FILE__ "unfold" "Bad toplevel expr form."



and exec_var exec_info v =
  match v with
  | FnVariable vi ->
    begin
      (* Is the variable a state variable ?*)
      if VarSet.has_vid exec_info.context.state_vars vi.vid then
        try
          IM.find vi.vid exec_info.state_exprs, ES.empty
        with Not_found ->
          (Format.eprintf "@.%sERROR%s \
                           I was searching for an expression for variable \
                           id %s%i%s in map %a@."
             (PpTools.color "red") PpTools.color_default
             (PpTools.color "red") vi.vid  PpTools.color_default
             (fun fmt map -> PpTools.ppimap FPretty.pp_fnexpr fmt map)
             exec_info.state_exprs);
          exception_on_variable "Expression not found for state variable" v
      else
        begin
          (* Is the variable an index variable ? *)
          if VarSet.has_vid exec_info.context.index_vars vi.vid then
            try
              IM.find vi.vid exec_info.index_exprs, ES.empty
            with Not_found ->
              exception_on_variable "Expression not found for index" v
          else
            (**
               It is a scalar input variable, we have to check if this
               variable has been used previously, if not we create a
               new variable for this use.
            *)
            FnVar v, ES.singleton (FnVar v)
        end
    end
  | FnArray (v', offset_expr) ->
    begin
      match v' with
      | FnVariable vi when VarSet.has_vid exec_info.context.state_vars vi.vid ->
        (try
           let vect = IM.find vi.vid exec_info.state_exprs in
           match unfold_expr exec_info offset_expr, vect with
           | (FnConst (CInt k), re) , FnVector ar -> Array.get ar k , re
           | _ ->
             failhere __FILE__ "exec_var" "Index non ineger or array expression not vector"
         with Not_found ->
           failhere __FILE__ "exec_var" "Not found: vector expression.")
      | _ ->
        let new_v' =
          match exec_var exec_info v' with
          | FnVar v, _-> v
          | bad_v, _ ->
            exception_on_expression "Unexpected variable form in exec_var" bad_v
        in
        let new_offset, new_reads = unfold_expr exec_info offset_expr in
        FnVar (FnArray (new_v', new_offset)),
        ES.union (ES.singleton (FnVar (FnArray (new_v', new_offset))))
          new_reads
    end

and unfold_expr ?(loc = -1) exec_info expr  =
  let rcall = unfold_expr exec_info in
  match expr with
  (* Where all the work is done : when encountering an expression in
       the function*)

  | FnVar v -> exec_var exec_info v

  | FnConst c -> expr, ES.empty

  (* Recursive cases with only expressions as subexpressions *)
  | FnFun sklet -> expr, ES.empty (* TODO recursive *)

  | FnBinop (binop, e1, e2) ->
    let e1', r1 = rcall e1 in
    let e2', r2 = rcall e2 in
    let rset = ES.union r1 r2 in
    partial_interpret (FnBinop(binop, e1', e2')), rset

  | FnCond (c, e1, e2) ->
    let c', rc = rcall c in
    let e1', r1 = rcall e1 in
    let e2', r2 = rcall e2 in
    partial_interpret (FnCond (c', e1', e2')), ES.union rc (ES.union r1 r2)

  | FnUnop (unop, expr') ->
    let e, r = rcall expr' in
    partial_interpret (FnUnop (unop, e)), r

  | FnApp (sty, vi_o, elist) ->
    let erlist = List.map  (rcall) elist in
    let elist', rlist = ListTools.unpair erlist in
    FnApp (sty, vi_o, elist'),
    List.fold_left (fun r es -> ES.union r es) ES.empty rlist

  | FnAddrof expr' | FnStartOf expr'
  | FnAlignofE expr' | FnSizeofE expr' ->
    rcall expr'

  | FnSizeof _ | FnSizeofStr _ | FnAlignof _ ->
    expr, ES.empty

  | FnCastE (sty, expr') ->
    let e, r = rcall expr' in
    FnCastE (sty, e), r

  (* Special cases where we have irreducible conditionals and nested for
     loops*)
  | FnRec ((i, g, u), s0, sklet) ->
    print_endline "TODO: s0 ignored in Loop function";
    let emap, reads = unfold_loop exec_info loc i g u sklet in
    (* Update once tuples are supported. *)
    let _, e = IM.max_binding emap in
    (match e with
    | FnVector ar ->
      (if loc > 0 then Array.get ar loc else e), reads
    | _ -> e, reads)


  | FnAddrofLabel _ | _ ->
    failwith "Unsupported expression in variable discovery algorithm"


and unfold_loop exec_info loc i g u (s, body) =
  let indexvar = VarSet.max_elt (used_in_fnexpr u) in
  (* TODO redo this part correctly *)
  let i0, iEnd =
    match i with
    | FnConst (CInt c) -> c, 0
    | _ ->
      (Format.printf "%sAssuming loop is leftwards.%s@."
        (PpTools.color "blue") PpTools.color_default);
      0, !_arsize_ - 1
  in
  let i0', iEnd' =
    match g with
    | FnBinop (Lt, i, FnConst (CInt c))
    | FnBinop (Gt, FnConst (CInt c), i) ->
      0, c
    | FnBinop (Lt, FnConst (CInt c), i)
    | FnBinop (Gt, i, FnConst (CInt c)) ->
      c, 0
    | _ -> 0, !_arsize_
  in
  let i0, iEnd = min i0 i0' , max iEnd iEnd' in
  let current_index = ref 0 in
  let body_i = replace_expression ~in_subscripts:true
      ~to_replace:(FnVar (FnVariable indexvar))
      ~by:(FnConst (CInt !current_index))
      ~ine:body
  in
  let rec exec_loop (new_exprs, read_exprs) exec_info k =
    if k >= iEnd then
      new_exprs, read_exprs
    else
      let e', r' = (unfold IM.empty exec_info body_i) in
      exec_loop (e', r')
        {exec_info with
         state_exprs = IM.update_all exec_info.state_exprs e';
         inputs = ES.union r' exec_info.inputs} (k + 1)
  in
  exec_loop (IM.empty, ES.empty) exec_info 0


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
  if silent then () else incr GenVars.exec_count;
  unfold IM.empty exec_info inp_func
