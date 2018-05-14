open Beta

val join_loop_width : int ref
val debug : bool ref

val build_join : FuncTypes.fnExpr list -> VarSet.t ->
  FuncTypes.fnExpr -> (FuncTypes.fnExpr * FuncTypes.fnExpr) -> FuncTypes.fnExpr
val build_for_inner :
  FuncTypes.fnExpr list -> VarSet.t ->
  FuncTypes.fnExpr Utils.IM.t -> FuncTypes.fnExpr ->
  (FuncTypes.fnExpr * FuncTypes.fnExpr) -> FuncTypes.fnExpr
