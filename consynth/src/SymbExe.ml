open Utils
open Cil
    
module Ty = SketchTypes

(*Keep track of the generated names during symbolic execution *)
type symbolic_input = (string * Cil.exp)

let genvars = ref IM.empty
let init () = genvars := IM.empty
let find_from_exp cexp =
  let same_exp =
    IM.filter
      (fun vid (vname, vexp) ->
         if vexp = cexp then true else false)
      !genvars
  in
  IM.max_binding same_exp

let exec_once stv exprs func index_expr =
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
      IM.add vid (exec_exp expr) exprs (* TODO : update the corresponding expression *)
    | Ty.SkArray (v, e) ->
      failwith
        "Unsupported arrays in state variables for variable discovery algorithm"
  and exec_exp expr = expr
  in
  exec exprs func
    
      
    
