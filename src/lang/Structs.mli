open Base
open Typ

val get : string -> typ option

val save : unit -> unit

val restore : unit -> unit

val add_name : string -> (string * typ) list -> unit

val type_of_fields : (string * typ) list -> typ option

val decl_anonymous : (string * typ) list -> unit

val decl_of_vars : (string * typ) list -> string

val is_anonymous : typ -> bool

val name_of_fields : (string * typ) list -> string option

val field_type : string -> string -> typ option

val is_struct_type : typ -> bool

val dump_state : unit -> unit
