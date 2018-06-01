open FuncTypes

val verbose : bool ref
val replace_by_join : prob_rep -> prob_rep list -> prob_rep
val no_join_inlined_body : prob_rep -> fnExpr
val inline_inner : int -> prob_rep -> prob_rep
