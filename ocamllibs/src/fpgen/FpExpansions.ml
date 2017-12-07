open Format
open SketchTypes
open SymbExe
open Utils

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
*)
let needs_superacc (sketch : sketch_rep) =
  (* Which are the variables who need superaccumulators? *)
  let is_accumulated i (expr : skExpr) : bool =
    match expr with
    | SkBinop(Plus, _, _) -> true
    | _ -> false
  in
  let which_accumulators (exprmap : skExpr IM.t) =
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
                     (VSOps.vidset_of_vs (used_in_skexpr expr))
                     (IM.keyset acc_map))
                  )))) expr_map
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
                 inputs = T.ES.empty }
  in
  let expr_map, _ = unfold_once init_i func in
  let acc_map = which_accumulators expr_map in
  (* ----------- DEBUG -------- *)
  if !debug then
    printf "%sDEBUG%s: expressions accumulated:@.%a@."
      (Ppt.color "red") Ppt.color_default
      (Ppt.ppimap SPretty.pp_skexpr) acc_map;
  (* -------------------------- *)
  let needs_cache = which_cached acc_map expr_map in
  ()




(**
 *  MAIN ENTRY POINT - Generate the structure that represents
 *  the header file for the floating point expansion.
 *)
let gen_header (sketch : sketch_rep) =
  (* ----------- DEBUG -------- *)
  if !debug then
    printf "@.%sDEBUG%s: Generating header for %s(%i) in %s@."
      (Ppt.color "red") Ppt.color_default
      sketch.loop_name sketch.id sketch.host_function.C.svar.C.vname;
  (* -------------------------- *)
  needs_superacc sketch
