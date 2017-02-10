val left_auxiliaries : Utils.VS.t ref
val right_auxiliaries : Utils.VS.t ref
val debug : bool ref
val auxiliary_variables : Cil.varinfo Utils.IH.t
val build : Utils.VS.t -> SketchTypes.sklet -> SketchTypes.sklet
