open Pretty
open List
open Printf
open Format
open Utils

module SketchBody = SketchBody
module SketchJoin = SketchJoin

(** Main interface for code analysis and sketch generation *)
module Canalyst : sig
  open Cil
  open SketchTypes
  type figu = Utils.VS.t * (Cil2Func.letin * Cil2Func.expr * Cil2Func.letin)
  type func_info =
    string * int list * Usedef.VS.t * Usedef.VS.t *
    Cil2Func.letin * figu * (Cil.constant Utils.IM.t)

  type sigu = Utils.VS.t * (sklet * skExpr * sklet)

  val processFile: string -> Findloops.Cloop.t Utils.IM.t

  val cil2func : Findloops.Cloop.t Utils.IM.t -> func_info list

  val func2sketch : func_info list -> sketch_rep list

  val find_new_variables : sketch_rep -> sketch_rep

  val pp_sketch : Format.formatter -> sketch_rep  -> unit
end

module PpHelper : sig
  (** GIven a color name return the color prefix for printing *)
  val color : string -> string

  (** Default color code for printing *)
  val default : string

  (** Pretty print a list given a pretty printer for the elements, a separator
      (default is ;) *)
  val ppli : formatter -> ?sep:string -> (formatter -> 'a -> unit) ->
    ('a list -> unit)

  (** Prretty print a list of integers *)
  val pp_int_list : formatter -> int list -> unit

  (** Print a list of integers to the standard output defined by
      Format.std_formatter *)
  val print_int_list : int list -> unit

  (** Pretty print the elements of an integer map given a pretty printer for the
      elements of the map *)
  val ppimap : (formatter -> 'a -> unit) -> formatter -> ('a IM.t -> unit)

  (** Output a string representing a Cil location *)
  val string_of_loc : Cil.location -> string

  (** Deserialize a string repsenting a CIl location *)
  val loc_of_string : string -> Cil.location option

  (** Print an error message in red to the Format.err_formatter *)
  val printerr : string -> unit
end

module Sketch : sig
  module Body = SketchBody
  module Join = SketchJoin

  (** Main interface to print the sketch of the whole problem.
      @param fmt A Format.formatter
      @param read A list of variable ids representing the subset of read-only
      variables.
      @param state A list of variables ids representing the set of state
      variables.
      @param all_vars The set of all the variables in the problem.
      @param loop_body The loop body in a functional form.
      @param join_body The sketch of the join for the loop body.
      @param idx The set of index variables.
      @param i The iniitalization of the index.
      @param g AN expression containinf only index variables representing the
      termination condition of the loop.
      @param u A function updating the index from one iteration to another.
      @param reach_consts A mapping from variable IDs to expressions. If a binding
      from a variable id to an expression exists, then the value of the variable
      will be set to this expression in the inital state of the loop.
  *)
  val pp_rosette_sketch : Format.formatter ->
    (int list * int list * Utils.VS.t *
     SketchTypes.sklet * SketchTypes.sklet *
     (Utils.VS.t * (SketchTypes.sklet * SketchTypes.skExpr * SketchTypes.sklet)) *
     (SketchTypes.skExpr Utils.IM.t)) -> unit
end

module Utils : sig
  module S = Str

  module IntHash : sig
    type t = int val equal : 'a -> 'a -> bool val hash : int -> int
  end

  module IH : sig
    type key = IntHash.t
    type 'a t = 'a Hashtbl.Make(IntHash).t
    val create : int -> 'a t
    val clear : 'a t -> unit
    val reset : 'a t -> unit
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
    val find_all : 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length : 'a t -> int
    val stats : 'a t -> Hashtbl.statistics
  end

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

  val v2e : Cil.varinfo -> Cil.exp
  val (|>) : 'a -> ('a -> 'b) -> 'b
  val map_2 : ('a -> 'b) -> ('a * 'a) -> ('b * 'b)
  val map_3 : ('a -> 'b) -> ('a * 'a * 'a) -> ('b * 'b * 'b)
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b

  val bool_of_int64 : Int64.t -> bool

  val str_contains : string -> string -> bool

  module ListTools : sig
    val (--): int -> int -> int list
    val intlist_max : int list -> int
    val lmin : ('a-> int) -> 'a list -> 'a
    val foldl_union : ('a -> VS.t) -> 'a list -> VS.t
    val foldl_union2 : ('a -> VS.t * VS.t) -> 'a list -> (VS.t * VS.t)
    val pair : 'a list -> 'b list -> ('a * 'b) list
    val unpair : ('a * 'b) list -> 'a list * 'b list
    val outer_join_lists : 'a list * 'a list -> 'a list
    val last : 'a list -> 'a
    val replace_last : 'a list -> 'a -> 'a list
    val remove_last : 'a list -> 'a list
  end

  val last_instr : Cil.stmt -> Cil.instr
  val check_option : 'a option -> 'a
  val maybe_apply : ('a -> 'b) -> 'a option -> 'b option
  val maybe_apply_default : ('a -> 'b) -> 'a option -> 'b -> 'b
  val xorOpt : 'a option -> 'a option -> 'a option
  val get_fun : Cil.file -> string -> Cil.fundec option
  val non_empty_block : Cil.block -> bool
  val global_filter_only_func : (Cil.fundec -> unit) -> Cil.global -> unit
  val global_filter_only_funcLoc :
    (Cil.fundec -> Cil.location -> unit) -> Cil.global -> unit
  val appendC : 'a list -> 'a -> 'a list

  module CilTools : sig
    open Cil
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
    val fun_ret_type : Cil.typ -> Cil.typ option
    val is_of_bool_type : Cil.typ -> bool
    val is_of_real_type : Cil.typ -> bool
    val is_of_int_type : Cil.typ -> bool
    val combine_expression_option :
      Cil.binop -> Cil.exp option -> Cil.exp option -> Cil.typ -> Cil.exp option
    val gen_var_with_suffix : Cil.varinfo -> string -> Cil.varinfo
    val gen_var_with_prefix : Cil.varinfo -> string -> Cil.varinfo
  end

  module VSOps : sig
    val sovi : Cil.instr -> VS.t
    val sove : Cil.exp -> VS.t
    val sovv : ?onlyNoOffset:bool -> Cil.lval -> VS.t
    val sovoff : Cil.offset -> VS.t

    val bindings : VS.t -> (int * VS.elt) list
    val of_bindings : (int * VS.elt) list -> VS.t

    val varlist : VS.t -> VS.elt list
    val of_varlist : VS.elt list -> VS.t

    val namelist : VS.t -> string list
    (* Membership testing : using variable id or an Lvalue that is a variable *)
    val has_vid : int -> VS.t -> bool
    val has_lval : Cil.lval -> VS.t -> bool
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
    val vs_with_prefix : VS.t -> string -> VS.t
    (* Pretty-printing functions *)
    val pp_var_names : Format.formatter -> VS.t -> unit
    val to_string : VS.t -> string
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
    val disjoint_sets : 'a  IM.t -> 'b IM.t ->
      ('a IM.t * 'b IM.t * 'a IM.t * 'b IM.t)
  end

  module SMTools : sig
    val update : 'a SM.t -> SM.key -> 'a -> ('a -> 'a -> 'a) -> 'a SM.t
  end
end

module SketchTypes : sig
  type sklet =
    | SkLetExpr of (skLVar * skExpr) list
    (**  (let ([var expr]) let)*)
    | SkLetIn of (skLVar * skExpr) list * sklet

  and skLVar =
    | SkVarinfo of Cil.varinfo
    (** Access to an array cell *)
    | SkArray of skLVar * skExpr
    | SkTuple of VS.t


  and skExpr =
    | SkVar of skLVar
    | SkConst of constants
    | SkFun of sklet
    | SkRec of  Findloops.forIGU * sklet
    | SkCond of skExpr * sklet * sklet
    | SkBinop of symb_binop * skExpr * skExpr
    | SkUnop of symb_unop * skExpr
    | SkApp of symbolic_type * (Cil.varinfo option) * (skExpr list)
    | SkQuestion of skExpr * skExpr * skExpr
    | SkHoleL of skLVar * symbolic_type
    | SkHoleR of symbolic_type
    (** Simple translation of Cil exp needed to nest
        sub-expressions with state variables *)
    | SkSizeof of symbolic_type
    | SkSizeofE of skExpr
    | SkSizeofStr of string
    | SkAlignof of symbolic_type
    | SkAlignofE of skExpr
    | SkCastE of symbolic_type * skExpr
    | SkAddrof of skExpr
    | SkAddrofLabel of Cil.stmt ref
    | SkStartOf of skExpr

  (** Structure types for Rosette sketches *)

  and initial_defs =
    | Initials of (string * string) list [@@deriving_sexp]

(**
   The body of the join and the loop are Racket programs with
   holes insides.
*)
and racket_with_holes = string list [@@deriving_sexp]

(**
   A state is simply a list of variables that are modified
   during the loop.
*)
and state = string list [@@deriving_sexp]

(**
   We generate the body of the oririginal loop simply from
   the state variables and the list of function that are
   applied to each state variable.
*)
and body_func =
    | DefineBody of state * racket_with_holes
  | DefineJoin of state * racket_with_holes
[@@deriving_sexp]

(** Interface types with Rosette/Racket *)

and symbolic_type =
    | Bottom | Num
    | Unit
    (** Base types : only booleans, integers and reals *)
    | Integer
    | Real
    | Boolean
    (** Type tuple *)
    | Tuple of symbolic_type list
    (** Other lifted types *)
    | Bitvector of int
    (** A function in Rosette is an uniterpreted function *)
    | Function of symbolic_type * symbolic_type
    (** A procdedure is a reference to a procedure object *)
    | Procedure of symbolic_type * symbolic_type
    (** Pairs and lists *)
    | Pair of symbolic_type
    | List of symbolic_type * int option
    (** Vector and box *)
    | Vector of symbolic_type * int option
    | Box of symbolic_type
    (** User-defined structures *)
    | Struct of symbolic_type



(*
  Operators : Cil operators and C function names.
*)

and symb_unop =
    | Not | Add1 | Sub1
    (**
       From C++11 : 4 different ops.
       value   round   floor   ceil    trunc
       -----   -----   -----   ----    -----
       2.3     2.0     2.0     3.0     2.0
       3.8     4.0     3.0     4.0     3.0
       5.5     6.0     5.0     6.0     5.0
       -2.3    -2.0    -3.0    -2.0    -2.0
       -3.8    -4.0    -4.0    -3.0    -3.0
       -5.5    -6.0    -6.0    -5.0    -5.0
    *)
    | Abs | Floor | Ceiling | Truncate | Round
    | Neg
    (** Misc*)
    | Sgn
    | UnsafeUnop of symb_unsafe_unop

and symb_binop =
    (** Booleans*)
    | And | Nand | Or | Nor | Implies | Xor
    (** Integers and reals *)
    | Plus | Minus | Times | Div | Quot | Rem | Mod
    (** Max and min *)
    | Max | Min
    (** Comparison *)
    | Eq | Lt | Le | Gt | Ge | Neq
    (** Shift*)
    | ShiftL | ShiftR
    | Expt
    | UnsafeBinop of symb_unsafe_binop

(**
   Some racket function that are otherwise unsafe
   to use in Racket, but we might still need them.
*)
and symb_unsafe_unop =
    (** Trigonometric + hyp. functions *)
    | Sin | Cos | Tan | Sinh | Cosh | Tanh
    (** Anti functions *)
    | ASin | ACos | ATan | ASinh | ACosh | ATanh
    (** Other functions *)
    | Log | Log2 | Log10
    | Exp | Sqrt


and symb_unsafe_binop =
    | TODO

(** Some pre-defined constants existing in C99 *)
and constants =
    | CNil
  | CInt of int
  | CInt64 of int64
  | CReal of float
  | CBool of bool
  | CBox of Cil.constant
  | CChar of char
  | CString of string
  | CUnop of symb_unop * constants
  | CBinop of symb_binop * constants * constants
  | CUnsafeUnop of symb_unsafe_unop * constants
  | CUnsafeBinop of symb_unsafe_binop * constants * constants
  | Infnty | NInfnty
  | Pi | SqrtPi
  | Sqrt2
  | Ln2 | Ln10 | E

val symb_unop_of_cil : Cil.unop -> symb_unop * symbolic_type
val symb_binop_of_cil : Cil.binop -> symb_binop * symbolic_type
val symb_type_of_ciltyp : Cil.typ -> symbolic_type
val symb_type_of_cilconst : Cil.constant -> symbolic_type
val ciltyp_of_symb_type : symbolic_type -> Cil.typ option

val type_of_const : constants -> symbolic_type
val type_of_var : skLVar -> symbolic_type
val type_of : skExpr -> symbolic_type

val rec_expr :
  ('a -> 'a -> 'a) ->
  'a ->
  (skExpr -> bool) ->
  (skExpr -> 'a) -> (constants -> 'a) -> (skLVar -> 'a) -> skExpr -> 'a
val transform_expr :
  (skExpr -> bool) ->
  ((skExpr -> skExpr) -> skExpr -> skExpr) ->
  (constants -> constants) -> (skLVar -> skLVar) -> skExpr -> skExpr

val scm_to_sk :
  Cil.varinfo Utils.SM.t -> Ast.expr -> sklet option * skExpr option
end
