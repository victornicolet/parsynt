open Cil

type func_info =
  int list * int list * Usedef.VS.t *
    Cil2Func.letin * (Cil.constant Utils.IM.t)

type sketch_info =
  int list * int list * Usedef.VS.t * SketchTypes.sklet *
     SketchTypes.sklet * (SketchTypes.skExpr Utils.IM.t)

val processFile: string -> Findloops.Cloop.t Utils.IM.t

val cil2func : Findloops.Cloop.t Utils.IM.t -> func_info list

val func2sketch : func_info list -> sketch_info list

val pp_sketch : Format.formatter -> sketch_info  -> unit
