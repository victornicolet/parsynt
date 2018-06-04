open Beta
open FuncTypes

val debug : bool ref
val verbose : bool ref
val store_solution : prob_rep option -> unit
val build_join : fnExpr list -> VarSet.t -> fnExpr ->
  (fnExpr * fnExpr) -> fnExpr
val build_for_inner : fnExpr list -> VarSet.t -> fnExpr Utils.IM.t -> fnExpr ->
  (fnExpr * fnExpr) -> fnExpr
