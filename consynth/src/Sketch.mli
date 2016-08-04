val build_body : Cil2Func.letin -> Utils.VS.t -> SketchTypes.sklet
val build_join : SketchTypes.sklet -> Utils.VS.t -> SketchTypes.sklet
val convert_const : Cil.constant -> SketchTypes.skExpr

val pp_rosette_sketch : Format.formatter ->
  (int list * int list * Utils.VS.t *
     SketchTypes.sklet * SketchTypes.sklet *
     (SketchTypes.skExpr Utils.IM.t)) -> unit
