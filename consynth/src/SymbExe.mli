open Utils
module Ty = SketchTypes

val exec_once :
  VS.t -> Ty.skExpr IM.t -> Ty.sklet -> Ty.skExpr -> Ty.skExpr IM.t
val rewrite : VS.t -> Ty.skExpr list -> Ty.skExpr list
