val quiet : bool ref

val verbose : bool ref

val verb_debug : int ref

val verb_warning : bool ref

val submsg_on : bool ref

val indent : unit -> string

val error : unit Fmt.t -> unit

val info : unit Fmt.t -> unit

val debug : ?level:int -> unit Fmt.t -> unit

val success : unit Fmt.t -> unit

val warning : ?level:int -> unit Fmt.t -> unit

val warning_msg : ?level:int -> string -> unit

val error_msg : string -> unit

val debug_msg : ?level:int -> string -> unit

val info_msg : string -> unit

val success_msg : string -> unit

val print_res_timing : string -> int -> int -> int -> float -> float -> float -> float -> unit

val print_res_unsat : string -> float -> unit

val print_res_error : string -> float -> unit
