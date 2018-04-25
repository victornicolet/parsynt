val cur_left_auxiliaries : FuncTypes.VarSet.t ref
val cur_right_auxiliaries : FuncTypes.VarSet.t ref
val add_laux_id:int -> unit
val add_raux_id:int -> unit
val is_left_aux : int -> bool
val is_right_aux : int -> bool
val debug : bool ref
val auxiliary_variables : FuncTypes.fnV Sets.IH.t
val build : FuncTypes.fnExpr -> FuncTypes.VarSet.t -> FuncTypes.fnExpr -> FuncTypes.fnExpr
