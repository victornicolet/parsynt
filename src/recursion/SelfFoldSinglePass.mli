val to_single_pass :
  (Lang.Term.VarSet.t * Lang.Typ.term) list ->
  Lang.Typ.term * Lang.Term.VarSet.t ->
  ( Lang.SolutionDescriptors.soln_info,
    float * (Lang.Term.VarSet.t * Lang.Typ.term) list * Lang.Typ.term )
  Base.Either.t

val solve : Lang.SolutionDescriptors.soln_info -> Lang.SolutionDescriptors.join_soln list
