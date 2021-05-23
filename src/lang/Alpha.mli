val reserved : string list

val init : unit -> unit

val get_new_name : ?suffix:string -> string -> string

val get_new_id : unit -> int

val add_name : string -> unit