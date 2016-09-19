open Utils
module Ty = SketchTypes
module IM = Utils.IM 

val exec_once : VS.t -> Ty.skExpr IM.t -> Ty.sklet -> Ty.skExpr IM.t
val rewrite : VS.t -> Ty.skExpr list
