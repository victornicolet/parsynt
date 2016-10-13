open Utils
open Cil
open SError

module T = SketchTypes
module Ct = CilTools

type exec_info =
  { state_set : VS.t;
    state_exprs : T.skExpr IM.t;
    index_set : VS.t;
    index_exprs : T.skExpr IM.t;
  }

(** --------------------------------------------------------------------------*)
(*Keep track of the generated names during symbolic execution *)
type symbolic_input = (int * string * T.skLVar)

let scalar_default_offset = -1
let genvars = IH.create 30

(* Add variable to the map with a vid key and offset key *)
let add_to_genvars vid offset vname subst =
  IH.add genvars vid (offset, vname, subst)

(* Find variable id with offset (for arrays or default offset for scalars)*)
let find_vid_offset vid offset =
  let symb_inp_list = IH.find_all genvars vid in
  List.find (fun (off, vn, e) -> off = offset) symb_inp_list


let exec_count = ref 0

let init () =
  IH.clear genvars;
  exec_count := 0

(* Find a variable that has the same expression. We want to avoid to create
   two different variable name for the same input (case of arrays if we access
   the same cell, we don't want to create two differnt symbols).
*)
let find_from_exp vid cexp =
  let symb_inp_list = IH.find_all genvars vid in
  let same_exp =
    List.find_all
      (fun (offset, vname, (vexp, nexp)) -> vexp = cexp)
      symb_inp_list
  in
  if List.length same_exp < 1 then
    raise Not_found
  else
    List.nth same_exp 0

(** From a sketch variable, generate a new name and a new variable
    and memorize the old expression and the new expression of the
    variable.
    @param v the variable expression, a SkLVar
    @return the offset of the varaible corresponding to the number of
    expansions realised, the new name of the variable and a pair
    representing the substituion of the expression in the code by
    the new expression of the variable.
*)

let rec gen_var v =
  try
    let host_vi = check_option (T.vi_of v) in
    try
      find_from_exp host_vi.vid v
    with Not_found ->
      let vname = host_vi.vname in
      let new_vi = Ct.gen_var_with_suffix host_vi (string_of_int !exec_count) in
      let new_v = T.SkVarinfo new_vi in
      let offset =
        match v with
        | T.SkState -> scalar_default_offset
        | T.SkVarinfo _ -> scalar_default_offset
        | T.SkArray _ -> !exec_count
      in
      add_to_genvars host_vi.vid offset vname (v, new_v);
      (offset, new_vi.vname, (v,new_v))
  with Failure s ->
    raise
      (Failure
         (Format.fprintf Format.str_formatter
            "%s@.Variable:%a@.Initial message: %s@."
            "Failed to find host variable in gen_var"
            SPretty.pp_sklvar v
            s;
          Format.flush_str_formatter ()))

(* Filter out the new variable part in the variable generation output *)
let gen_expr v =
  let _, _, (_, ev) = gen_var v in T.SkVar ev

let declared_vars () =
  IH.fold
    (fun i (offset, vname, (v, new_v)) vs ->
       let vi = T.vi_of new_v in
       if is_some vi then VS.add {(check_option vi) with vname = vname} vs
       else vs)
    genvars VS.empty

(** --------------------------------------------------------------------------*)
(** Intermediary functions for exec_once *)
let rec exec exec_info func =
  let rec  apply_let_exprs let_list exec_info =
    List.fold_left (update_expressions exec_info) IM.empty let_list

  and update_expressions exec_info new_exprs (var, expr) =
    (* TODO : find the new expression of a variable by
       replacing every state variable in expr by the corresponding expression
       in exprs and introducing new read variables. *)
    match var with
    | T.SkState -> exec_info.state_exprs
    | T.SkVarinfo vi ->
      let vid = vi.vid in
      IM.add vid (exec_expr exec_info expr) new_exprs
    | T.SkArray (v, e) ->
      exception_on_variable
        "Unsupported arrays in state variables for variable discovery algorithm."
        v
  in
  match func with
  | T.SkLetExpr let_list ->
    apply_let_exprs let_list exec_info
  | T.SkLetIn (let_list, let_cont) ->
    let new_exprs = apply_let_exprs let_list exec_info in
    exec {exec_info with state_exprs = new_exprs} let_cont



and exec_var exec_info v =
  match v with
  | T.SkState -> T.SkVar v

  | T.SkVarinfo vi ->
    begin
      (* Is the variable a state variable ?*)
      if VSOps.has_vid vi.vid exec_info.state_set then
        try
          IM.find vi.vid exec_info.state_exprs
        with Not_found ->
          exception_on_variable "Expression not found for state variable" v
      else
        begin
          (* Is the variable an index variable ? *)
          if VSOps.has_vid vi.vid exec_info.index_set then
            try
              IM.find vi.vid exec_info.index_exprs
            with Not_found ->
              exception_on_variable "Expression not found for index" v
          else
            (** It is a scalar input variable, we have to check if this
                 variable has been used previously, if not we create a
                 new variable for this use.
            *)
            gen_expr v
        end
    end
  | T.SkArray (v', offset_expr) ->
    (** TODO : add support for arrays in state variables. For now,
        we assume all state variables are scalars, so if we have
        an array in an expression it is necessarily an input variable.
    *)
    begin
      let new_v' =
        match exec_var exec_info v' with
        | T.SkVar v -> v
        | bad_v ->
          exception_on_expression "Unexpected variable form in exec_var" bad_v
      in
      let new_offset = exec_expr exec_info offset_expr in
      T.SkVar (T.SkArray (new_v', new_offset))
    end

and exec_expr exec_info expr =
  match expr with
  (* Where all the work is done : when encountering an expression in
       the function*)

  | T.SkVar v -> exec_var exec_info v

  | T.SkConst c -> expr

  (* Recursive cases with only expressions as subexpressions *)
  | T.SkFun sklet -> expr (* TODO recursive *)
  | T.SkBinop (binop, e1, e2) ->
    let e1' = exec_expr exec_info e1 in
    let e2' = exec_expr exec_info e2 in
    T.SkBinop (binop, e1', e2')

  | T.SkQuestion (c, e1, e2) ->
    let c' = exec_expr exec_info c in
    let e1' = exec_expr exec_info e1 in
    let e2' = exec_expr exec_info e2 in
    T.SkQuestion (c', e1', e2')

  | T.SkUnop (unop, expr') -> T.SkUnop (unop, exec_expr exec_info expr')
  | T.SkApp (sty, vi_o, elist) ->
    let elist' = List.map (exec_expr exec_info) elist in
    T.SkApp (sty, vi_o, elist')

  | T.SkAddrof expr' | T.SkStartOf expr'
  | T.SkAlignofE expr' | T.SkSizeofE expr' -> exec_expr exec_info expr'
  | T.SkSizeof _ | T.SkSizeofStr _ | T.SkAlignof _ -> expr
  | T.SkCastE (sty, expr') -> T.SkCastE (sty, exec_expr exec_info expr')
  (* Special cases where we have irreducible conitionals and nested for
     loops*)
  | T.SkRec ((i, g, u), sklet) -> expr (* TODO recusrive + test on IGU *)
  | T.SkCond (c, letif, letelse) -> expr (* TODO recursive *)
  | T.SkAddrofLabel _ | _ ->
    failwith "Unsupported expression in variable discovery algorithm"

(** exec_once : simulate the applciation of a function body to a set of
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
let exec_once ?(silent = false) exec_nfo inp_func =
  if silent then () else incr exec_count;
  exec exec_nfo inp_func
