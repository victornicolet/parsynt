open Format
open Cil

open SketchTypes
open SPretty
open Utils
open Utils.PpTools


(* Generates synthetic join and loop functions *)

type hdef_file = hdef_loop * hdef_join

and hdef_loop =
  {
    args : Cil.varinfo list;
    llocals : Cil.varinfo list;
    lreturns : Cil.varinfo list;
    lbody: Cil.block;
  }
and hdef_join =
  {
    argsl : Cil.varinfo list;
    argsr : Cil.varinfo list;
    jlocals : Cil.varinfo list;
    jreturns : Cil.varinfo list;
    jbody: Cil.block;
  }

type sketch_rep = {
  id : int;
  host_function : Cil.fundec;
  loop_name : string;
  ro_vars_ids : int list;
  scontext : SketchTypes.context;
  min_input_size : int;
  uses_global_bound : bool;
  loop_body : SketchTypes.sklet;
  join_body : SketchTypes.sklet;
  join_solution : SketchTypes.sklet;
  init_values : Ast.expr Utils.IM.t;
  sketch_igu : SketchTypes.sigu;
  reaching_consts : SketchTypes.skExpr Utils.IM.t;
}

let pp_argslist f fmt args = ppli fmt ~sep:", " f args

let pp_typed_arg fmt varinfo =
  fprintf fmt "%a %s" CilTools.fppt varinfo.vtype varinfo.vname

let pp_untyped_arg fmt vi =
  fprintf fmt "%s" vi.vname

let pp_hdef_loop fmt hloop =
  fprintf fmt "sequential(%a) returns (%a) locals (%a) {%a}@."
    (pp_argslist pp_typed_arg) hloop.args
    (pp_argslist pp_untyped_arg) hloop.lreturns
    (pp_argslist pp_untyped_arg) hloop.llocals
    CilTools.fppbk hloop.lbody

let pp_hdef_join fmt hjoin =
  fprintf fmt "join(%a | %a) returns (%a) locals (%a) {%a}@."
    (pp_argslist pp_typed_arg) hjoin.argsl
    (pp_argslist pp_typed_arg) hjoin.argsr
    (pp_argslist pp_untyped_arg) hjoin.jreturns
    (pp_argslist pp_untyped_arg) hjoin.jlocals
    CilTools.fppbk hjoin.jbody

let pp_hdef_file fmt (hdefl, hdefj) =
  fprintf fmt "%a@.%a@." pp_hdef_loop hdefl pp_hdef_join hdefj

let from_sketch_rep sr =
  let hloop =
    let args = sr.scontext.state_vars in
    let returns = sr.scontext.state_vars in
    let locals = sr.scontext.all_vars in
    let body = sr.loop_body in
    {
      args = VSOps.varlist args ;
      lreturns = VSOps.varlist returns;
      llocals = VSOps.varlist locals;
      lbody = Cil.mkBlock([])
    }
  in
  let hjoin =
    let args = sr.scontext.state_vars in
    let returns = sr.scontext.state_vars in
    let locals = sr.scontext.all_vars in
    let body = sr.loop_body in
    {
      argsl = VSOps.varlist (VSOps.vs_with_prefix args "l");
      argsr = VSOps.varlist (VSOps.vs_with_prefix args "r");
      jreturns = VSOps.varlist returns;
      jlocals = VSOps.varlist locals;
      jbody = Cil.mkBlock([])
    }
  in
  (hloop, hjoin)
