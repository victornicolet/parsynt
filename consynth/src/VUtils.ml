open Format
open Utils
open SPretty
open SketchTypes
open SymbExe
open Expressions
open ExpressionReduction

let debug = ref false

module C = Cil

type auxiliary =
  {
    avarinfo : C.varinfo;
    aexpr : skExpr;
    afunc : skExpr;
    depends : VS.t;
  }


let same_aux old_aux new_aux =
  if IM.cardinal old_aux != IM.cardinal new_aux
  then false
  else
    IM.fold
      (fun n_vid n_aux same ->
         try
           (let o_aux = IM.find n_vid old_aux in
            if o_aux.afunc = n_aux.afunc then true && same else false)
         with Not_found -> false)
      new_aux
      true

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
      (fun vid aux ->
         not (is_already_computed xinfo (vid, aux_vs, aux.afunc) exprs))
      aux_ef
  in
  (VS.filter (fun vi -> IM.mem vi.C.vid new_aux_ef) aux_vs), new_aux_ef


let reduction_with_warning stv expset expr =
  let reduced_expression = reduce_full stv expset expr in
  if (expr = reduced_expression) && !debug then
    begin
      Format.fprintf Format.std_formatter
        "%sWarning%s : expression @;%a@; unchanged after \
         reduction with state %a @; and expressions %a @."
        (PpHelper.color "red") PpHelper.default
        SPretty.pp_skexpr reduced_expression
        VSOps.pvs stv
        (fun fmt a -> SPretty.pp_expr_set fmt a) expset
    end
  else ();
  reduced_expression
