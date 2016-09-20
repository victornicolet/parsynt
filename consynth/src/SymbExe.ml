open Utils
open Cil

module Ty = SketchTypes
module Ct = CilTools

(** --------------------------------------------------------------------------*)
(*Keep track of the generated names during symbolic execution *)
type symbolic_input = (int * string * Ty.skLVar)

let scalar_default_offset = -1
let genvars = IH.create 30

(* Add variable to the map with a vid key and offset key *)
let add_to_genvars vid offset vname expr =
  IH.add genvars vid (offset, vname, expr)

(* Find variable id with offset (for arrays or default offset for scalars)*)
let find_vid_offset vid offset =
  let symb_inp_list = IH.find_all genvars vid in
  List.find (fun (off, vn, e) -> off = offset) symb_inp_list


let exec_count = ref 0

let init () =
  IH.clear genvars;
  exec_count := 0

let find_from_exp vid cexp =
  let symb_inp_list = IH.find_all genvars vid in
  let same_exp =
    List.find_all
      (fun (offset, vname, vexp) -> vexp = cexp)
      symb_inp_list
  in
  if List.length same_exp < 1 then
    raise Not_found
  else
    List.nth same_exp 0

let gen_var v =
  match v with
  | Ty.SkVarinfo vi ->
    begin
      try
        find_from_exp vi.vid v
      with Not_found ->
        let vname = vi.vname in
        let new_vi = Ct.gen_var_with_suffix vi (string_of_int !exec_count) in
        add_to_genvars vi.vid scalar_default_offset vname v;
        (scalar_default_offset, new_vi.vname, v)
    end
  | _ ->
    failwith "Bad input variable in gen_var"

let gen_expr v =
  let _, _, ev = gen_var v in Ty.SkVar ev

(** --------------------------------------------------------------------------*)

let exec_once stv exprs func index_expr =
  incr exec_count;
  (* Simply replace the occurrences of state variables
     in the function by the expression corresponding
     to the state variable and introduce new symbolic
     read variables in place of the read variables.
  *)
  let rec exec exprs func =
    match func with
    | Ty.SkLetExpr let_list ->
      apply_let_exprs let_list exprs
    | Ty.SkLetIn (let_list, let_cont) ->
      let new_exprs = apply_let_exprs let_list exprs in
      exec new_exprs let_cont

  and apply_let_exprs let_list old_exprs =
    List.fold_left (update_expressions old_exprs) IM.empty let_list

  and update_expressions old_exprs new_exprs (var, expr) =
    (* TODO : find the new expression of a variable by
       replacing every state variable in expr by the corresponding expression
       in exprs and introducing new read variables. *)
    match var with
    | Ty.SkState -> exprs
    | Ty.SkVarinfo vi ->
      let vid = vi.vid in
      IM.add vid (exec_exp old_exprs expr) exprs (* TODO : update the corresponding expression *)
    | Ty.SkArray (v, e) ->
      failwith
        "Unsupported arrays in state variables for variable discovery algorithm"

  and exec_exp old_exprs expr =
    match expr with
    (* Where all the work is done : when encountering an expression in
       the function*)

    | Ty.SkVar v ->
      begin
        match v with
        | Ty.SkState -> expr
        | Ty.SkVarinfo vi ->
          begin
            if VSOps.has_vid vi.vid stv then
              IM.find vi.vid old_exprs
            else
              (* It is a scalar input variable, we have to check if this variable
                 has been used previously, if not we create a new variable for
                 this use.
              *)
              gen_expr v
          end
        | _ ->
          gen_expr v

      end

    | Ty.SkConst c -> expr

    (* Recursive cases with only expressions as subexpressions *)
    | Ty.SkFun sklet -> expr (* TODO recursive *)
    | Ty.SkBinop (binop, e1, e2) ->
      let e1' = exec_exp old_exprs e1 in
      let e2' = exec_exp old_exprs e2 in
      Ty.SkBinop (binop, e1', e2')

    | Ty.SkQuestion (c, e1, e2) ->
      let c' = exec_exp old_exprs c in
      let e1' = exec_exp old_exprs e1 in
      let e2' = exec_exp old_exprs e2 in
      Ty.SkQuestion (c', e1', e2')

    | Ty.SkUnop (unop, expr') -> Ty.SkUnop (unop, exec_exp old_exprs expr')
    | Ty.SkApp (sty, vi_o, elist) ->
      let elist' = List.map (exec_exp old_exprs) elist in
      Ty.SkApp (sty, vi_o, elist')

    | Ty.SkAddrof expr' | Ty.SkStartOf expr'
    | Ty.SkAlignofE expr' | Ty.SkSizeofE expr' -> exec_exp old_exprs expr'
    | Ty.SkSizeof _ | Ty.SkSizeofStr _ | Ty.SkAlignof _ -> expr
    | Ty.SkCastE (sty, expr') -> Ty.SkCastE (sty, exec_exp old_exprs expr')


    (* Special cases where we have irreducible conitionals and nested for
       loops*)
    | Ty.SkRec ((i, g, u), sklet) -> expr (* TODO recusrive + test on IGU *)
    | Ty.SkCond (c, letif, letelse) -> expr (* TODO recursive *)

    | Ty.SkAddrofLabel _ | _ ->
      failwith "Unsupported expression in variable discovery algorithm"

  in
  exec exprs func

let rewrite state expr_list = expr_list
