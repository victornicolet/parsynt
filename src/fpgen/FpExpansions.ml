open Format
open FuncTypes
open SymbExe
open Utils

open FpNames

module Ppt = Utils.PpTools
module C = Cil

let debug = ref true


type fpexp_vars = {
  saccs : C.varinfo list;
  caches : C.varinfo list;
  other_vars : C.varinfo list;
}

type fpexp_precise_op = {
  replaced_op : string;
}

type fpexpansion_header = {
  vars : fpexp_vars;
}


(**
   Evaluate the expression assigned to a variable. If the top operator of the
   resulting expression is an addition then we need a superaccumulator and a
   cache for it.
   @param sketch the representation of the function. This should be a solved
                 sketch, meaning that the join solution is not empty.
   @returns A pair, the first element are the variables that need
            superaccumulators and the second element are the variables
            that need a cache (a floating point expansion).
*)
let needs_extension sketch =
  (* Which are the variables who need superaccumulators? *)
  let is_accumulated i (expr : fnExpr) : bool =
    match expr with
    | FnBinop(Plus, _, _) -> true
    | _ -> false
  in
  let which_accumulators (exprmap : fnExpr IM.t) =
    IM.filter is_accumulated exprmap
  in
  (* Which are the variables who need caching? *)
  let which_cached acc_map expr_map =
    (* Variables that use an accumulated variables should be cached, saving
       precision in the flaoting point representation *)
    IM.filter
      (fun i expr ->
         (not (IM.mem i acc_map) &&
          (not (IS.is_empty
                  (IS.inter
                     (IS.of_list (VarSet.vids_of_vs (used_in_fnexpr expr)))
                     (IM.keyset acc_map))
               ))))
      expr_map
  in
  let ctx = sketch.scontext in
  let func = sketch.loop_body in
  (* ----------- DEBUG -------- *)
  if !debug then
    printf "%sDEBUG%s: Searching superaccumulator uses.@."
      (Ppt.color "red") Ppt.color_default;
  (* -------------------------- *)
  let init_i = { context = ctx;
                 state_exprs = create_symbol_map ctx.state_vars;
                 index_exprs = create_symbol_map ctx.index_vars;
                 inputs = ES.empty }
  in
  let expr_map, _ = unfold_once init_i func in
  let acc_map = which_accumulators expr_map in
  (* ----------- DEBUG -------- *)
  if !debug then
    printf "%sDEBUG%s: expressions accumulated:@.%a@."
      (Ppt.color "red") Ppt.color_default
      (Ppt.ppimap FPretty.pp_fnexpr) acc_map;
  (* -------------------------- *)
  let needs_superacc = IM.keyset acc_map in
  let needs_cache =
    IS.union (IM.keyset (which_cached acc_map expr_map)) needs_superacc
  in
  (VarSet.iset sketch.scontext.state_vars (IS.elements needs_superacc),
   VarSet.iset sketch.scontext.state_vars (IS.elements needs_cache))




(**
 *  MAIN ENTRY POINT - Generate the structure that represents
 *  the header file for the floating point expansion.
 *)
let gen_header sketch =
  (* ----------- DEBUG -------- *)
  if !debug then
    printf "@.%sDEBUG%s: Generating header for %s(%i) in %s@."
      (Ppt.color "red") Ppt.color_default
      sketch.loop_name sketch.id sketch.host_function.fvar.vname;
  (* -------------------------- *)
  let needs_superacc, needs_cache =  needs_extension sketch in
  ( )
