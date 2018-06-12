open Beta
open FuncTypes

val debug : bool ref
val verbose : bool ref
val store_solution : prob_rep option -> unit

val sketch_join : prob_rep -> prob_rep
val sketch_inner_join : prob_rep -> prob_rep

val match_hole_to_completion: fnExpr -> fnExpr -> fnExpr option
