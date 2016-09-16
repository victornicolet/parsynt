open Cil
open Pretty
open List
open Printf
open Format


module S = Str
module IH = Inthash

module IM : sig
  type key = int
  type +'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val mem : key -> 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val singleton : key -> 'a -> 'a t
  val remove : key -> 'a t -> 'a t
  val merge :
    (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val for_all : (key -> 'a -> bool) -> 'a t -> bool
  val exists : (key -> 'a -> bool) -> 'a t -> bool
  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
  val cardinal : 'a t -> int
  val bindings : 'a t -> (key * 'a) list
  val min_binding : 'a t -> key * 'a
  val max_binding : 'a t -> key * 'a
  val choose : 'a t -> key * 'a
  val split : key -> 'a t -> 'a t * 'a option * 'a t
  val find : key -> 'a t -> 'a
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
end

module IS : sig
  type elt = int
  type t
  val empty : t
  val is_empty : t -> bool
  val mem : elt -> t -> bool
  val add : elt -> t -> t
  val singleton : elt -> t
  val remove : elt -> t -> t
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val subset : t -> t -> bool
  val iter : (elt -> unit) -> t -> unit
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool
  val filter : (elt -> bool) -> t -> t
  val partition : (elt -> bool) -> t -> t * t
  val cardinal : t -> int
  val elements : t -> elt list
  val min_elt : t -> elt
  val max_elt : t -> elt
  val choose : t -> elt
  val split : elt -> t -> t * bool * t
  val find : elt -> t -> elt
  val of_list : elt list -> t
end

module SM : sig
  type key = String.t
  type 'a t = 'a Map.Make(String).t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val mem : key -> 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val singleton : key -> 'a -> 'a t
  val remove : key -> 'a t -> 'a t
  val merge :
    (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val for_all : (key -> 'a -> bool) -> 'a t -> bool
  val exists : (key -> 'a -> bool) -> 'a t -> bool
  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
  val cardinal : 'a t -> int
  val bindings : 'a t -> (key * 'a) list
  val min_binding : 'a t -> key * 'a
  val max_binding : 'a t -> key * 'a
  val choose : 'a t -> key * 'a
  val split : key -> 'a t -> 'a t * 'a option * 'a t
  val find : key -> 'a t -> 'a
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
end

module VS = Usedef.VS
              
val ih_of_vs : VS.t -> VS.elt IH.t
val ih_join_left : ('a * 'b option) IH.t -> 'a IH.t -> 'b IH.t -> unit

val identity : 'a -> 'a
val identity2 : 'a -> 'b -> 'b

val is_some : 'a option -> bool
val is_none : 'a option -> bool 

val v2e : varinfo -> exp
val (|>) : 'a -> ('a -> 'b) -> 'b
val map_2 : ('a -> 'b) -> ('a * 'a) -> ('b * 'b)
val map_3 : ('a -> 'b) -> ('a * 'a * 'a) -> ('b * 'b * 'b)
val fst : 'a * 'b -> 'a
val snd : 'a * 'b -> 'b

val bool_of_int64 : Int64.t -> bool

module ListTools : sig
  val (--): int -> int -> int list
  val intlist_max : int list -> int
  val foldl_union : ('a -> VS.t) -> 'a list -> VS.t
  val foldl_union2 : ('a -> VS.t * VS.t) -> 'a list -> (VS.t * VS.t)
  val pair : 'a list -> 'b list -> ('a * 'b) list
  val unpair : ('a * 'b) list -> 'a list * 'b list
  val outer_join_lists : 'a list * 'a list -> 'a list
  val last : 'a list -> 'a
  val replace_last : 'a list -> 'a -> 'a list
  val remove_last : 'a list -> 'a list
end

val last_instr : stmt -> instr
val check_option : 'a option -> 'a
val maybe_apply : ('a -> 'b) -> 'a option -> 'b option
val maybe_apply_default : ('a -> 'b) -> 'a option -> 'b -> 'b
val xorOpt : 'a option -> 'a option -> 'a option
val get_fun : file -> string -> fundec option
val non_empty_block : block -> bool
val global_filter_only_func : (fundec -> unit) -> global -> unit
val global_filter_only_funcLoc :
  (fundec -> location -> unit) -> global -> unit
val appendC : 'a list -> 'a -> 'a list

module CilTools : sig
  val psprint80 : (unit -> 'a -> Pretty.doc) -> 'a -> string
  val ppe : exp -> unit
  val ppt : typ -> unit
  val pps : stmt -> unit
  val pplv : lval -> unit
  val ppv : varinfo -> unit
  val ppi : instr -> unit
  val ppbk : block -> unit
  val ppofs : offset -> unit

  val is_literal_zero : exp -> bool
  val add_stmt : Cil.block -> Cil.stmt list -> Cil.block
  val simplify_rds : ('a * 'b * 'c) option -> 'c option
  val neg_exp : exp -> exp
  val is_like_array : varinfo -> bool
  val is_like_bool : ikind -> bool
  val combine_expression_option :
    Cil.binop -> Cil.exp option -> Cil.exp option -> Cil.typ -> Cil.exp option
end

module VSOps : sig
  val sovi : instr -> VS.t
  val sove : exp -> VS.t
  val sovv : ?onlyNoOffset:bool -> Cil.lval -> VS.t
  val sovoff : offset -> VS.t

  val bindings : VS.t -> (int * VS.elt) list
  val of_bindings : (int * VS.elt) list -> VS.t

  val varlist : VS.t -> VS.elt list
  val of_varlist : VS.elt list -> VS.t

  val namelist : VS.t -> string list
  (* Membership testing : using variable id or an Lvalue that is a variable *)
  val has_vid : int -> VS.t -> bool
  val has_lval : lval -> VS.t -> bool
  val find_by_id : int -> VS.t -> VS.elt
  (* Take the subset of input set corresponding to the ids in the list*)
  val subset_of_list : int list -> VS.t -> VS.t
  (* Return the list of the variable ids *)
  val vids_of_vs : VS.t -> int list
  (* Return the union of a list of sets *)
  val unions : VS.t list -> VS.t
  (* Return the union of the sets created by mapping the function
     over the list *)
  val union_map  : 'a list -> ('a -> VS.t) -> VS.t
  (* Return the set of variables defined in the Reaching 
     definitions type of Cil *)
  val vs_of_defsMap : (Cil.varinfo * Reachingdefs.IOS.t option) IH.t -> VS.t
  val vs_of_inthash : VS.elt IH.t -> VS.t
  (* Append suffix to names in input variable set.*)
  val vs_with_suffix : VS.t -> string -> VS.t
  (* Pretty-printing functions *)
  val pp_var_names : Format.formatter -> VS.t -> unit
  val pvs : Format.formatter -> VS.t -> unit
  val ppvs : VS.t -> unit
  val spvs : VS.t -> string
  val epvs : VS.t -> unit

  val string_of_vs : VS.t -> string    
end

module IHTools : sig
  val add_all : 'a IH.t -> 'a IH.t -> unit
  val add_list : 'a IH.t -> ('a -> int) -> 'a list -> unit
  val iter_bottom_up :
    'a IH.t -> ('a -> bool) -> ('a -> 'a list) -> ('a -> unit) -> 'a list
end

module IMTools : sig
  val add_all : 'a IM.t -> 'a IM.t -> 'a IM.t
  val inter : 'a IM.t -> 'a IM.t -> 'a IM.t
  val is_disjoint :
    ?non_empty:(IM.key -> 'a -> bool) -> 'b IM.t -> 'a IM.t -> bool
end

module SMTools : sig
  val update : 'a SM.t -> SM.key -> 'a -> ('a -> 'a -> 'a) -> 'a SM.t
end
