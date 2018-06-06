val silent_racket_command_string : string -> string
val err_handler_sketch : 'a -> unit
val pp_struct_definition :
  ?transparent:bool -> Format.formatter -> string *string list -> unit
val pp_struct_equality :
  Format.formatter -> string * string list -> unit
val pp_comment : Format.formatter -> string -> unit
val pp_join_body_app :
  Format.formatter ->
  string * string * ('a list * 'b * 'c * int) * int * int ->
  unit
val pp_mless_body_app :
  Format.formatter -> string * string * int -> unit

type rosette_hole_type =
  | HArith
  | HNonLinear
  | HBasicNum
  | HBoolean
  | HComparison
  | HNumIte
  | HScalarExpr

val hole_type_name : rosette_hole_type -> string

type rosette_operator_choice =
  | OCComparison
  | OCScalar
  | OCBasicNum
  | OCArith
  | OCNonLinear
  | OCBoolean
  | OCUnopsNum

val operator_choice_name : rosette_operator_choice -> string

val parse_scm : string -> RAst.expr list
