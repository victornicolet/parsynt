module Build = BuildSketch

val pp_rosette_sketch : Format.formatter ->
  (int list * int list * Utils.VS.t *
     SketchTypes.sklet * SketchTypes.sklet *
     (SketchTypes.skExpr Utils.IM.t)) -> unit
