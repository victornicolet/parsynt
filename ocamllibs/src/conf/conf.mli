(** General settings *)
val get_conf_string: string -> string
(** Builtin variables *)
type builtins =
  | Min_Int
  | Max_Int
  | False
  | True
val is_builtin_var: string -> bool
val get_builtin: string -> builtins
(** Verification parameters *)
val verification_parameters : (int * int * int) list
(** Grammar macros *)
val get_hole_type_name: string -> string
val get_operator_choice: string -> string
val is_hole_type: string -> bool
val is_op_choice: string -> bool
val get_kw_list: unit -> string list
