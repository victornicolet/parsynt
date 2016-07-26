open Cil

val processFile: string -> Loops.Cloop.t Utils.IM.t
val cil2func : Loops.Cloop.t Utils.IM.t ->
  (int list * int list * Usedef.VS.t * Cil2Func.letin) Utils.IM.t
val func2sketch :
  (int list * int list * Usedef.VS.t * Cil2Func.letin) Utils.IM.t ->
  (int list * int list * Usedef.VS.t * SketchTypes.sklet *
     SketchTypes.sklet) Utils.IM.t

val pp_sketch : Format.formatter ->
  int list * int list * Usedef.VS.t * SketchTypes.sklet * SketchTypes.sklet
  -> unit
