open FuncTypes

val verbose : bool ref
val replace_by_join : prob_rep -> prob_rep list -> prob_rep
val inline_inner : prob_rep -> prob_rep
