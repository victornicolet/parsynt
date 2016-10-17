open Utils
open Cil
open SError

module T = SketchTypes
module Ct = CilTools
module ES = T.ES

type exec_info =
  { state_set : VS.t;
    state_exprs : T.skExpr IM.t;
    index_set : VS.t;
    index_exprs : T.skExpr IM.t;
    inputs : T.ES.t
  }



(** --------------------------------------------------------------------------*)
(** Intermediary functions for exec_once *)
let rec exec exec_info func =
  let rec apply_let_exprs let_list exec_info =
    List.fold_left (update_expressions exec_info) (IM.empty, T.ES.empty) let_list

  and update_expressions exec_info (new_exprs, read_exprs) (var, expr) =
    match var with
    | T.SkState -> exec_info.state_exprs, read_exprs
    | T.SkVarinfo vi ->
      let vid = vi.vid in
      let nexpr, n_rexprs = exec_expr exec_info expr in
      IM.add vid nexpr new_exprs, T.ES.union n_rexprs read_exprs
    | T.SkArray (v, e) ->
      exception_on_variable
        "Unsupported arrays in state variables for variable discovery algorithm."
        v
  in
  match func with
  | T.SkLetExpr let_list ->
    apply_let_exprs let_list exec_info
  | T.SkLetIn (let_list, let_cont) ->
    let new_exprs, new_reads = apply_let_exprs let_list exec_info in
    exec {exec_info with state_exprs = new_exprs; inputs = new_reads} let_cont



and exec_var exec_info v =
  match v with
  | T.SkState -> T.SkVar v, ES.empty

  | T.SkVarinfo vi ->
    begin
      (* Is the variable a state variable ?*)
      if VSOps.has_vid vi.vid exec_info.state_set then
        try
          IM.find vi.vid exec_info.state_exprs, ES.empty
        with Not_found ->
          exception_on_variable "Expression not found for state variable" v
      else
        begin
          (* Is the variable an index variable ? *)
          if VSOps.has_vid vi.vid exec_info.index_set then
            try
              IM.find vi.vid exec_info.index_exprs, ES.empty
            with Not_found ->
              exception_on_variable "Expression not found for index" v
          else
            (** It is a scalar input variable, we have to check if this
                 variable has been used previously, if not we create a
                 new variable for this use.
            *)
            T.SkVar v, ES.singleton (T.SkVar v)
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
        | T.SkVar v, _-> v
        | bad_v, _ ->
          exception_on_expression "Unexpected variable form in exec_var" bad_v
      in
      let new_offset, new_reads = exec_expr exec_info offset_expr in
      T.SkVar (T.SkArray (new_v', new_offset)), ES.singleton (T.SkVar v)
    end

and exec_expr exec_info expr =
  match expr with
  (* Where all the work is done : when encountering an expression in
       the function*)

  | T.SkVar v -> exec_var exec_info v

  | T.SkConst c -> expr, T.ES.empty

  (* Recursive cases with only expressions as subexpressions *)
  | T.SkFun sklet -> expr, T.ES.empty (* TODO recursive *)
  | T.SkBinop (binop, e1, e2) ->
    let e1', r1 = exec_expr exec_info e1 in
    let e2', r2 = exec_expr exec_info e2 in
    T.SkBinop (binop, e1', e2'), ES.union r1 r2

  | T.SkQuestion (c, e1, e2) ->
    let c', rc = exec_expr exec_info c in
    let e1', r1 = exec_expr exec_info e1 in
    let e2', r2 = exec_expr exec_info e2 in
    T.SkQuestion (c', e1', e2'), ES.union rc (ES.union r1 r2)

  | T.SkUnop (unop, expr') ->
    let e, r = exec_expr exec_info expr' in
    T.SkUnop (unop, e), r

  | T.SkApp (sty, vi_o, elist) ->
    let erlist = List.map  (exec_expr exec_info) elist in
    let elist', rlist = ListTools.unpair erlist in
    T.SkApp (sty, vi_o, elist'),
    List.fold_left (fun r es -> ES.union r es) ES.empty rlist

  | T.SkAddrof expr' | T.SkStartOf expr'
  | T.SkAlignofE expr' | T.SkSizeofE expr' ->
    exec_expr exec_info expr'

  | T.SkSizeof _ | T.SkSizeofStr _ | T.SkAlignof _ ->
    expr, ES.empty

  | T.SkCastE (sty, expr') ->
    let e, r = exec_expr exec_info expr' in
    T.SkCastE (sty, e), r

  (* Special cases where we have irreducible conitionals and nested for
     loops*)
  | T.SkRec ((i, g, u), sklet) -> expr, ES.empty (* TODO recusrive + test on IGU *)
  | T.SkCond (c, letif, letelse) -> expr, ES.empty (* TODO recursive *)
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
  if silent then () else incr GenVars.exec_count;
  exec exec_nfo inp_func
