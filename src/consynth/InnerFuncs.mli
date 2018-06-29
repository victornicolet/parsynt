open Fn

val verbose : bool ref
val replace_by_join : prob_rep -> prob_rep list -> prob_rep
val no_join_inlined_body : prob_rep -> fnExpr
val inline_inner : ?index_variable:bool-> ?inline_pick_join:bool -> int -> prob_rep -> prob_rep
val update_inners_in_body:  (prob_rep * prob_rep) list -> fnExpr -> fnExpr
val uses_inner_join_func : fnExpr -> bool
