open Fn

val debug : bool ref

val verbose : bool ref

val store_solution : prob_rep option -> unit

val store_ctx_sol : string -> context * fnExpr -> unit

val get_inner_solution : string -> (context * fnExpr) option

val sketch_join : prob_rep -> prob_rep

val sketch_inner_join : prob_rep -> prob_rep

val match_hole_to_completion : fnExpr -> fnExpr -> fnExpr option
