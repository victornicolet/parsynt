open Utils
open SPretty
open SketchTypes
open SymbExe
open Expressions

module C = Cil


let is_already_computed xinfo (aux_id, aux_vs, func_expr) exprs =
  let candidate_state_variables =
    IM.filter
      (fun i e ->
         (* Replace auxiliary recursive call by state_expr *)
         let e_rep =
           replace_expression ~in_subscripts:false
             (SkVar (SkVarinfo (VSOps.find_by_id aux_id aux_vs)))
             (SkVar (SkVarinfo (VSOps.find_by_id i xinfo.state_set)))
             func_expr
         in
         eq_AC e_rep e) exprs
  in
  IM.cardinal candidate_state_variables > 0

let remove_duplicate_auxiliaries xinfo (aux_vs, aux_ef) input_func =
  let exprs, inputs = exec_once ~silent:true xinfo input_func in
  let new_aux_ef =
    IM.filter
      (fun vid (expr, func_expr) ->
         not (is_already_computed xinfo (vid, aux_vs, func_expr) exprs))
      aux_ef
  in
  (VS.filter (fun vi -> IM.mem vi.C.vid new_aux_ef) aux_vs), new_aux_ef
