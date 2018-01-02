open Utils
open Cil
open FError
open Expressions

module Fn = FuncTypes
module Ct = CilTools
module ES = Fn.ES


let debug = ref false

type exec_info =
  { context : Fn.context;
    state_exprs : Fn.fnExpr IM.t;
    index_exprs : Fn.fnExpr IM.t;
    inputs : Fn.ES.t  }

(** Create a mapping from variable ids to variable expressions to start the
    algorithm *)
let create_symbol_map vs=
  VS.fold
    (fun vi map -> IM.add vi.vid (Fn.FnVar (Fn.FnVarinfo vi)) map) vs IM.empty


(** --------------------------------------------------------------------------*)
(** Intermediary functions for exec_once *)
let rec unfold new_exprs exec_info func =

  let rec apply_let_exprs new_exprs let_list exec_info =
    List.fold_left
      update_expressions (new_exprs, exec_info.inputs) let_list

  and update_expressions (new_exprs, read_exprs) (var, expr) =
    match var with
    | Fn.FnTuple vs -> exec_info.state_exprs, read_exprs
    | Fn.FnVarinfo vi ->
      let vid = vi.vid in
      let nexpr, n_rexprs = unfold_expr exec_info expr in
      if !debug then
        (Format.fprintf Format.std_formatter "Set of read exprs : %a@."
           (fun fmt a -> FPretty.pp_expr_set fmt a)
           (Fn.ES.union n_rexprs read_exprs))
      else
        ();
      IM.add vid nexpr new_exprs, Fn.ES.union n_rexprs read_exprs
    | Fn.FnArray (v, e) ->
      exception_on_variable
        "Unsupported arrays in state variables for variable discovery algorithm."
        v
  in
  match func with
  | Fn.FnLetExpr let_list ->
    apply_let_exprs new_exprs let_list exec_info
  | Fn.FnLetIn (let_list, let_cont) ->
    let new_exprs, new_reads = apply_let_exprs new_exprs let_list exec_info in
    unfold new_exprs
      {exec_info with
       state_exprs = IM.update_all exec_info.state_exprs new_exprs;
       inputs = ES.union new_reads exec_info.inputs} let_cont



and exec_var exec_info v =
  match v with
  | Fn.FnTuple vs -> Fn.FnVar v, ES.empty

  | Fn.FnVarinfo vi ->
    begin
      (* Is the variable a state variable ?*)
      if VS.has_vid vi.vid exec_info.context.Fn.state_vars then
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
          if VS.has_vid vi.vid exec_info.context.Fn.index_vars then
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
            Fn.FnVar v, ES.singleton (Fn.FnVar v)
        end
    end
  | Fn.FnArray (v', offset_expr) ->
    (** TODO : add support for arrays in state variables. For now,
        we assume all state variables are scalars, so if we have
        an array in an expression it is necessarily an input variable.
    *)
    begin
      let new_v' =
        match exec_var exec_info v' with
        | Fn.FnVar v, _-> v
        | bad_v, _ ->
          exception_on_expression "Unexpected variable form in exec_var" bad_v
      in
      let new_offset, new_reads = unfold_expr exec_info offset_expr in
      Fn.FnVar (Fn.FnArray (new_v', new_offset)),
      ES.union (ES.singleton (Fn.FnVar (Fn.FnArray (new_v', new_offset))))
        new_reads
    end

and unfold_expr exec_info expr =
  match expr with
  (* Where all the work is done : when encountering an expression in
       the function*)

  | Fn.FnVar v -> exec_var exec_info v

  | Fn.FnConst c -> expr, ES.empty

  (* Recursive cases with only expressions as subexpressions *)
  | Fn.FnFun sklet -> expr, ES.empty (* TODO recursive *)

  | Fn.FnBinop (binop, e1, e2) ->
    let e1', r1 = unfold_expr exec_info e1 in
    let e2', r2 = unfold_expr exec_info e2 in
    Fn.FnBinop (binop, e1', e2'), ES.union r1 r2

  | Fn.FnQuestion (c, e1, e2) ->
    let c', rc = unfold_expr exec_info c in
    let e1', r1 = unfold_expr exec_info e1 in
    let e2', r2 = unfold_expr exec_info e2 in
    Fn.FnQuestion (c', e1', e2'), ES.union rc (ES.union r1 r2)

  | Fn.FnUnop (unop, expr') ->
    let e, r = unfold_expr exec_info expr' in
    Fn.FnUnop (unop, e), r

  | Fn.FnApp (sty, vi_o, elist) ->
    let erlist = List.map  (unfold_expr exec_info) elist in
    let elist', rlist = ListTools.unpair erlist in
    Fn.FnApp (sty, vi_o, elist'),
    List.fold_left (fun r es -> ES.union r es) ES.empty rlist

  | Fn.FnAddrof expr' | Fn.FnStartOf expr'
  | Fn.FnAlignofE expr' | Fn.FnSizeofE expr' ->
    unfold_expr exec_info expr'

  | Fn.FnSizeof _ | Fn.FnSizeofStr _ | Fn.FnAlignof _ ->
    expr, ES.empty

  | Fn.FnCastE (sty, expr') ->
    let e, r = unfold_expr exec_info expr' in
    Fn.FnCastE (sty, e), r

  (* Special cases where we have irreducible conitionals and nested for
     loops*)
  | Fn.FnRec ((i, g, u), sklet) -> expr, ES.empty (* TODO recusrive + test on IGU *)
  | Fn.FnCond (c, letif, letelse) -> expr, ES.empty (* TODO recursive *)
  | Fn.FnAddrofLabel _ | _ ->
    failwith "Unsupported expression in variable discovery algorithm"

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
