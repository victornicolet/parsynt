module Body = SketchBody
module Join = SketchJoin

val pp_rosette_sketch : Format.formatter ->
  (int list * int list * Utils.VS.t *
   SketchTypes.sklet * SketchTypes.sklet *
   (Utils.VS.t * (SketchTypes.sklet * SketchTypes.skExpr * SketchTypes.sklet)) *
   (SketchTypes.skExpr Utils.IM.t)) -> unit
