open Utils
module Ty = SketchTypes
 

val exec_once : VS.t -> Ty.skExpr list -> Ty.sklet -> Ty.skExpr list
val rewrite : Vs.t -> Ty.skExpr list
