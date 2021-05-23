type acc_op = { s : Typ.variable; a : Typ.variable; body : Typ.term }

type otimes_op = { s : Typ.variable; a : Typ.variable; e : Typ.variable; body : Typ.term }

type soln_info = {
  synt_time : float;
  tmp_file_sk : string;
  tmp_file_out : string;
  func_name : string;
  func_input : Typ.variable;
  func_input_assert : Typ.term option;
  func_body : Typ.term;
  return_type_as_set : bool;
  return_type : Typ.typ;
  target_func_name : string;
  target_accum_type : Typ.typ;
  list_field_name : string option;
  init : Typ.term;
  pre : acc_op;
  post : acc_op;
  otimes : otimes_op;
}

type std_soln = {
  sf_func : Typ.variable;
  sf_input : Typ.variable * Typ.term option;
  sf_as_set : bool;
  sf_ret : Typ.typ;
  sf_li : string;
  sf_init : Typ.term;
  sf_pre : acc_op;
  sf_post : acc_op;
  sf_otimes : otimes_op;
}

type div_soln = {
  synt_time : float;
  solved : bool;
  x : Typ.variable;
  pivots : (Typ.variable * (Typ.variable * Typ.variable list) * Typ.term) list;
  partitions : (Typ.variable * Typ.term) list;
}

type pred_soln = {
  synt_time : float;
  tmp_file_sk : string;
  tmp_file_out : string;
  base : std_soln;
  predicate : Typ.variable list * Typ.term;
  budget : ResourceModel.cbudget;
  divide : div_soln option;
}

type join_soln = {
  synt_time : float;
  pred_synt_time : float;
  tmp_file_sk : string;
  tmp_file_out : string;
  base : std_soln;
  predicate : Typ.variable list * Typ.term;
  budget : ResourceModel.cbudget;
  divide : div_soln option;
  join : Typ.variable list * Typ.term;
}

val std_acc_op : acc_op -> acc_op

val std_otimes_op : otimes_op -> otimes_op

val term_of_div_soln : div_soln -> Typ.term

val get_pivots : div_soln -> Typ.variable list

val check_std_soln : std_soln -> unit

val reduce_si : soln_info -> Typ.typ -> std_soln

val transform_to_struct : soln_info -> Typ.typ -> Typ.typ * soln_info

val std_soln_info : soln_info -> std_soln

val oplus_of_soln : std_soln -> Typ.variable * Typ.variable * Typ.term

val pp_soln_info_func : Format.formatter -> soln_info -> unit

val pp_std_soln_func : Format.formatter -> std_soln -> unit

val add_join_to_pred_soln : pred_soln -> Typ.variable list * Typ.term -> join_soln

val add_div_synt_times : float -> pred_soln list -> pred_soln list

val pp_join_soln : Format.formatter -> join_soln -> unit

val dump_id : int ref

val dump_join_soln : join_soln -> unit

type eqn_info = {
  erhs : Typ.term;
  einit : Typ.term;
  edeps : Term.VarSet.t;
  ejoin : (Typ.term, Typ.term) Base.Either.t;
  elifts : Term.VarSet.t;
}

val pp_eqn_info : Format.formatter -> eqn_info -> unit

type l_eqns = {
  eqns : eqn_info Utils.IM.t;
  vars : Term.VarSet.t;
  lstate : Typ.variable;
  rstate : Typ.variable;
  x : Typ.variable;
  collection_inputs : Term.VarSet.t;
  predicate : Typ.term;
  assume_input : Typ.term option;
  liftings : Term.VarSet.t;
  synt_time_lift : float;
  synt_time_join : float;
}

type eqs_soln_info = {
  tmp_file_sk : string;
  tmp_file_out : string;
  join_name : string;
  init_name : string;
  func_name : string;
  func_info : l_eqns;
  sketching_level : int;
}

val _struct_creation_helper :
  Term.VarSet.t -> string * (string * Typ.typ) list * Typ.variable * Typ.variable

val _update_structs :
  ?addressing:(string -> string) ->
  ?forget:string list ->
  old:l_eqns ->
  new_l:Typ.variable ->
  new_r:Typ.variable ->
  string ->
  Typ.term ->
  Typ.term

val get_struct_name : l_eqns -> string

val get_init : l_eqns -> int -> Typ.term option

val get_rhs : l_eqns -> int -> Typ.term option

val get_join : l_eqns -> int -> Typ.term option

val get_deps : l_eqns -> Typ.variable -> Term.VarSet.t option

val get_deps_i : l_eqns -> int -> Term.VarSet.t option

val get_var : l_eqns -> int -> Typ.variable option

val eqn_same_deps : eqn_info -> eqn_info -> bool

val make_deps_transitive : l_eqns -> l_eqns

val is_indirect_dep : l_eqns -> eqn_info -> Term.VarSet.t -> bool

val get_lifts : l_eqns -> Typ.variable -> Term.VarSet.t option

val get_lifts_i : l_eqns -> int -> Term.VarSet.t option

val eqn_same_lifts : eqn_info -> eqn_info -> bool

val make_lifts_transitive : l_eqns -> l_eqns

val update_deps : l_eqns -> l_eqns

val update_struct_vars : Term.VarSet.t -> l_eqns -> l_eqns

val subs_state_v : ?state:Typ.variable option -> l_eqns -> Typ.term -> Typ.term

val subs_rstate_v : l_eqns -> Typ.term -> Typ.term

val subs_v_state : l_eqns -> Typ.term -> Typ.term

val l_eqns_mapvar :
  l_eqns -> (int, 'a, 'b) Base.Map.t -> f:(Typ.variable -> 'a -> 'c) -> (int, 'c, 'b) Base.Map.t

val fields_to_var : l_eqns -> (string * 'a) list -> 'a Utils.IM.t

val update_joins : ?only:Typ.variable list option -> l_eqns -> Typ.term Utils.IM.t -> l_eqns

val update_inits : ?only:Typ.variable list option -> l_eqns -> Typ.term Utils.IM.t -> l_eqns

val collect_conditionals : l_eqns -> (Typ.term, Term.Terms.comparator_witness) Base.Set.t

val collect_positive_conditionals : l_eqns -> Typ.term list

val maybe_to_lift : l_eqns -> Term.VarSet.t

val unsolved : l_eqns -> Term.VarSet.t

val apply_subs_to_eqn : (Typ.variable * Typ.term) list -> eqn_info -> eqn_info

val same_equation : Typ.variable * eqn_info -> Typ.variable * eqn_info -> bool

val constant_function : l_eqns -> Typ.variable * eqn_info -> (Typ.variable * Typ.term) option

val pre_clean_l_eqns : l_eqns -> l_eqns

val clean_l_eqns : l_eqns -> l_eqns

val post_clean_l_eqns :
  l_eqns -> Term.VarSet.t -> (Typ.variable, Term.Variable.comparator_witness) Base.Set.t

val pp_l_eqns : Format.formatter -> l_eqns -> unit

val pp_eqn : Format.formatter -> Typ.variable * Typ.term -> unit

val dump_eqns : l_eqns -> unit
