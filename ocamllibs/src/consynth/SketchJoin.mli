val cur_left_auxiliaries : Utils.VS.t ref
val cur_right_auxiliaries : Utils.VS.t ref
val add_laux_id:int -> unit
val add_raux_id:int -> unit
val is_left_aux : int -> bool
val is_right_aux : int -> bool
val debug : bool ref
val auxiliary_variables : Cil.varinfo Utils.IH.t
val build : Utils.VS.t -> SketchTypes.sklet -> SketchTypes.sklet
