val make_base_choice_of_var : Lang.Typ.variable -> Lang.Typ.term

val bool_choice : ?no_eq:bool -> ?purefunc:bool -> int -> Lang.Typ.term list -> Lang.Typ.term

val int_choice : ?nonzero:bool -> ?nonone:bool -> int -> Lang.Typ.term list -> Lang.Typ.term

val pivot_comp_choice :
  ?no_eq:bool -> int -> Lang.Typ.term list -> Lang.Typ.term list -> Lang.Typ.term

val emptychecks : ?with_base_c:bool -> Lang.Typ.term list -> Lang.Typ.term list

val div_cmp_choice : ?no_eq:bool -> int -> Lang.Typ.term list -> Lang.Typ.term list -> Lang.Typ.term

val diversify : ?seeds:Lang.Term.VarSet.t option -> Lang.Typ.term -> int -> Lang.Typ.term

val init_term :
  (Lang.Typ.term, Lang.Term.Terms.comparator_witness) Base.Set.t ->
  Lang.Term.VarSet.t ->
  Lang.Typ.term ->
  Lang.Typ.term

val out_of_predicate_expr :
  ?max_k:int -> Lang.Typ.term -> Lang.Typ.typ -> Lang.Typ.term list -> Lang.Typ.term

val make : Lang.SolutionDescriptors.eqs_soln_info -> string -> Lang.Typ.term
