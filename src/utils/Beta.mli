(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
*)

exception Tuple_fail            (* Tuples are not supported for the moment. *)
exception BadType of string

val failontype: string -> 'a

type operator_type =
  | Arith                       (* Arithmetic only *)
  | Basic                       (* Airthmetic and min/max *)
  | NonLinear                   (* Non-linear operators *)
  | NotNum                        (* Not a numeral operator *)

type fn_type =
  | Bottom
  | Num
  | Unit
  (** Base types : only booleans, integers and reals *)
  | Integer
  | Real
  | Boolean
  (** Type tuple *)
  | Record of string * (string * fn_type) list
  (** Other lifted types *)
  | Bitvector of int
  (** A function in Rosette is an uninterpreted function *)
  | Function of fn_type * fn_type
  (** A procdedure is a reference to a procedure object *)
  | Procedure of fn_type * fn_type
  (** Pairs and lists *)
  | Pair of fn_type
  | List of fn_type * int option
  (** Vector and box *)
  | Vector of fn_type * int option
  | Box of fn_type
  (** User-defined structures *)
  | Struct of fn_type


type symb_unop =
  | Not | Add1 | Sub1
  | Abs | Floor | Ceiling | Truncate | Round
  | Neg
  (** Misc*)
  | Sgn
  | UnsafeUnop of symb_unsafe_unop

(* Binary operators available in Rosette *)
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
   Some racket functions that are otherwise unsafe
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
  | CArrayInit of int * constants
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

val shstr_of_type : fn_type -> string

val type_of_binop_args : symb_binop -> fn_type
val type_of_unop_args : symb_unop -> fn_type

val type_of_ciltyp : Cil.typ -> fn_type
val type_of_args : (string * Cil.typ * Cil.attribute list) list option
  -> fn_type

val type_of_cilconst : Cil.constant -> fn_type
val ciltyp_of_symb_type : fn_type -> Cil.typ option


val pp_typ : Format.formatter -> fn_type -> unit

val is_subtype : fn_type -> fn_type -> bool
val join_types : fn_type -> fn_type -> fn_type

val res_type: fn_type -> fn_type
val array_type : fn_type -> fn_type
val matrix_type : fn_type -> fn_type
val is_array_type : fn_type -> bool
val is_matrix_type : fn_type -> bool
val is_record_type : fn_type -> bool

type fnV = {
  mutable vname : string;
  mutable vtype : fn_type;
  vinit : constants option;
  mutable vid : int;
  mutable vistmp : bool;
}

module VarSet:
sig
  type elt = fnV
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
  val find_by_id : t -> int -> elt
  val find_by_name : t -> string -> elt
  val vids_of_vs : t -> int list
  val has_vid : t -> int -> bool
  val bindings : t -> (int * elt) list
  val names : t -> string list
  val types : t -> fn_type list
  val record : t -> (string * fn_type) list
  val add_prefix : t -> string -> t
  val iset : t -> int list -> t
  val pp_var_names : Format.formatter -> t -> unit
  val pp_vs : Format.formatter -> t -> unit
end

type jcompletion = { cvi : fnV; cleft : bool; cright : bool; crec : bool }


module CS :
  sig
  type elt = jcompletion
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
  val of_vs : VarSet.t -> t
  val map : (elt -> elt) -> t -> t
  val _L : t -> t
  val _R : t -> t
  val _LorR : t -> t
  val _LRorRec : ?filt:(elt -> bool) -> t -> t
  val to_jc_list : t -> elt list
  val to_vs : t -> VarSet.t
  val pp_cs : string -> Format.formatter -> t -> unit
end

val register : string -> unit
val register_vi : Cil.varinfo -> unit
val register_vs : Utils.VS.t -> unit
val register_fnv : fnV -> unit
val register_varset : VarSet.t -> unit
val get_new_name: ?base:string -> string

val find_var_name : string -> fnV
val find_vi_name : string -> Cil.varinfo
val find_vi_name_id : string -> int -> Cil.varinfo
val find_var_name_id : string -> int -> fnV

val mkFnVar : string -> fn_type -> fnV

val rhs_prefix : string
val lhs_prefix : string

val is_left_state_varname : string -> string * bool * bool
val is_right_state_varname : string -> string * bool * bool

val create_boundary_variables : VarSet.t -> unit
val get_index_to_boundary : fnV -> fnV * fnV
val is_left_index_vi : fnV -> bool
val is_right_index_vi : fnV -> bool
val left_index_vi : fnV -> fnV
val right_index_vi : fnV -> fnV

val concretize_aux : (int -> fnV ->  'a -> 'a) -> 'a -> 'a
val add_left_auxiliary : fnV -> unit
val add_right_auxiliary : fnV -> unit
val add_laux_id : int -> unit
val add_raux_id : int -> unit
val is_right_aux_id : int -> bool
val is_left_aux_id : int -> bool

val is_left_aux : fnV -> bool
val is_right_aux : fnV -> bool

val aux_vars_init : unit -> unit
val is_currently_aux : fnV -> bool

val copy_aux_to : fnV Utils.IH.t -> unit
val discover_init: unit -> unit
val discover_clear : unit -> unit

val discover_add : fnV -> unit
val discover_save : unit -> unit

val record_name : ?only_by_type:bool -> ?seed:string -> VarSet.t -> string
val record_type : VarSet.t ->  fn_type
val is_name_of_struct : string -> bool
val get_struct : string -> (string * fn_type) list * VarSet.t
val state_var_name : VarSet.t -> string -> string

val record_map : VarSet.t -> (VarSet.elt -> 'a -> 'b) -> 'a Utils.IM.t -> 'b Utils.IM.t
val record_accessor : string -> fnV -> fnV
val is_struct_accessor : string -> bool

val mark_outer_used : fnV -> unit
