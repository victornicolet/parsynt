open Beta
open FuncTypes

val debug : bool ref
val verbose : bool ref
val store_solution : prob_rep option -> unit
val build_join : inner:bool -> fnExpr list -> VarSet.t -> fnExpr Utils.IM.t -> fnExpr ->
  (fnExpr * fnExpr) -> fnExpr

val match_hole_to_completion: fnExpr -> fnExpr -> fnExpr option
