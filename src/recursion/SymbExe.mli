val allow_nonlinear : bool ref

type unfoldings_result = {
  state_record_var : Lang.Term.VarSet.t;
  init_as_resource : Lang.ResourceModel.resource list;
  unfoldings : Lang.Unfold.unfoldings;
  solver : Solve.SolverForms.online_solver;
  ret_type : Lang.Typ.typ list;
}

val use_solver_eval : bool ref

val solver_of_unfoldings : Lang.Unfold.unfoldings -> Solve.SolverForms.online_solver option

val branching_eval :
  Solve.SolverForms.online_solver -> Lang.Unfold.env -> Lang.Typ.term -> Lang.Typ.term

val resources_of_symbs :
  Lang.Typ.typ -> Lang.Term.symbolic_define -> Lang.ResourceModel.resource list

val resources_of_symb_list : Lang.Term.symbolic_define list -> Lang.ResourceModel.resource list

type eqns_unfolding_result = {
  zero_unfolding : Lang.Unfold.unfolding Utils.IM.t;
  eqns_unfoldings : Lang.Unfold.unfolding Utils.IM.t list;
  resources : Lang.ResourceModel.resource list;
  solver : Solve.SolverForms.online_solver;
}

val eqns_unfoldings : Lang.SolutionDescriptors.l_eqns -> eqns_unfolding_result

type sfsp_unfolding_result = {
  zero_unfolding : Lang.Unfold.unfolding;
  eqns_unfoldings : Lang.Unfold.unfolding list;
  resources : Lang.ResourceModel.resource list;
  solver : Solve.SolverForms.online_solver;
}

val pp_sfsp_unfolding_result : Format.formatter -> sfsp_unfolding_result -> unit

val reset : unit -> unit

val sfsp_unfoldings : Lang.SolutionDescriptors.std_soln -> sfsp_unfolding_result

val dependencies :
  Lang.Typ.term ->
  Lang.Typ.typ list ->
  Lang.Typ.typ ->
  ((int * int list) list, Sexplib0.Sexp.t) result
