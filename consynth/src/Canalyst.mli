open Cil
module T = SketchTypes

type figu = Utils.VS.t * (Cil2Func.letin * Cil2Func.expr * Cil2Func.letin)
type func_info =
  int list * int list * Usedef.VS.t *
  Cil2Func.letin * figu * (Cil.constant Utils.IM.t)

type sigu = Utils.VS.t * (T.sklet * T.skExpr * T.sklet)
type sketch_info =
  int list * int list * Usedef.VS.t * T.sklet *
     T.sklet * sigu * (T.skExpr Utils.IM.t)

val processFile: string -> Findloops.Cloop.t Utils.IM.t

val cil2func : Findloops.Cloop.t Utils.IM.t -> func_info list

val func2sketch : func_info list -> sketch_info list

val pp_sketch : Format.formatter -> sketch_info  -> unit
