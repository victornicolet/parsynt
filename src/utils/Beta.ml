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

open Utils
open Format

(**
   1 - Basic function types.
   2 - Variables management.
   3 - General variable names.
   4 - Left and right state variables.
   5 - Indexes.
   6 - Auxiliary variables.
   7 - Nested loops - outer state variables.
   8 - Records.
*)

(* -------------------- 1 - BASIC FUNCTION TYPES -------------------- *)

(** Internal type for building funces *)
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

and fnV = {
  mutable vname : string;
  mutable vtype : fn_type;
  vinit : constants option;
  mutable vid : int;
  mutable vistmp : bool;
}


and symb_unop =
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


let type_of_binop_args : symb_binop -> fn_type =
  function
  | Rem | Mod | Quot | Expt
  | Lt | Gt | Ge | Le | Max | Min
  | Plus | Minus | Times | Div  -> Num
  | Xor | And | Nand | Nor | Or | Implies -> Boolean
  | _ -> Unit

let type_of_unop_args : symb_unop -> fn_type=
  function
  | Not -> Boolean
  | _ -> Num


exception Tuple_fail            (* Tuples are not supported for the moment. *)
exception BadType of string

let failontype s = raise (BadType s)

let rec type_of_ciltyp =
  function
  | Cil.TInt (ik, _) ->
    begin
      match ik with
      | Cil.IBool -> Boolean
      | _ -> Integer
    end

  | Cil.TFloat _ -> Real

  | Cil.TArray (t, _, _) ->
    Vector (type_of_ciltyp t, None)

  | Cil.TFun (t, arglisto, _, _) ->
    Procedure (type_of_args arglisto, type_of_ciltyp t)
  | Cil.TComp (ci, _) -> Unit
  | Cil.TVoid _ -> Unit
  | Cil.TPtr (t, _) ->
    Vector (type_of_ciltyp t, None)
  | Cil.TNamed (ti, _) ->
    type_of_ciltyp ti.Cil.ttype
  | Cil.TEnum _ | Cil.TBuiltin_va_list _ -> failwith "Not implemented"

and type_of_args argslisto =
  try
    let argslist = check_option argslisto in
    let symb_types_list, argnames =
      List.map
        (fun (s, t, atr) -> type_of_ciltyp t)
        argslist,
      List.map
        (fun (s, t, atr) -> s)
        argslist
    in
    match symb_types_list with
    | [] -> Unit
    | [st] -> st
    | _ -> Record ("args", List.combine argnames symb_types_list)
  with Failure s -> Unit

let rec type_of_cilconst c =
  match c with
  | Cil.CInt64 _  | Cil.CChr _ -> Integer
  | Cil.CReal _ -> Real
  | Cil.CStr _ | Cil.CWStr _ -> List (Integer, None)
  | Cil.CEnum (_, _, einf) -> failwith "Enum types not implemented"

let rec ciltyp_of_symb_type =
  function
  | Integer -> Some (Cil.TInt (Cil.IInt, []))
  | Boolean -> Some (Cil.TInt (Cil.IBool, []))
  | Real | Num -> Some (Cil.TFloat (Cil.FFloat, []))
  | Vector (t, _) ->
    (match ciltyp_of_symb_type t with
     | Some tc -> Some (Cil.TArray (tc, None, []))
     | None -> None)
  | _ -> None




let rec pp_typ fmt t =
  let fpf = Format.fprintf in
  match t with
  | Unit -> fpf fmt "unit"
  | Bottom -> fpf fmt "<BOT>"
  | Integer -> fpf fmt "integer"
  | Real -> fpf fmt "real"
  | Num -> fpf fmt "num"
  | Boolean -> fpf fmt "boolean"
  | Vector (vt, _) -> fpf fmt "%a[]" pp_typ vt
  | Record (name, tl) ->
    fpf fmt "struct %s {%a}"
      name
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@;")
         (fun fmt (s,t) -> fprintf fmt "%s: %a" s pp_typ t)) tl
  | Function (argt, rett) ->
    fpf fmt "%a -> %a" pp_typ argt pp_typ rett
  | Pair t -> fpf fmt "%a pair" pp_typ t
  | List (t, _) -> fpf fmt "%a list" pp_typ t
  | Struct t -> fpf fmt "%a struct" pp_typ t
  | Bitvector i -> fpf fmt "bitvector[%i]" i
  | Box t -> fpf fmt "%a box" pp_typ t
  | Procedure (tin, tout) -> fpf fmt "(%a %a proc)" pp_typ tin pp_typ tout


let rec shstr_of_type t =
  match t with
  | Unit -> "u"
  | Bottom -> "o"
  | Integer -> "i"
  | Real -> "r"
  | Num -> "n"
  | Boolean -> "b"
  | Vector (vt, _) -> "V"^(shstr_of_type vt)^"_"
  | Record (name, tl) -> "R"^name
  | Function (argt, rett) -> "F"^(shstr_of_type argt)^"_"^(shstr_of_type rett)^"_"
  | _ ->
    pp_typ err_formatter t;
    failhere __FILE__ "shstr_of_type" "No short string for this type"

let rec is_subtype t tmax =
  match t, tmax with
  | t, tmax when t = tmax -> true
  | Integer, Real -> true
  | Num, Real | Real, Num -> true
  | Vector (t1', _), Vector(t2', _) -> is_subtype t1' t2'
  | Bottom, Integer -> true
  | _, _ -> false

let rec join_types t1 t2 =
  match t1, t2 with
  | t1, t2 when t1 = t2 -> t1
  | Integer, Boolean -> Boolean
  | Integer, Real | Real, Integer
  | Num, Real | Real, Num -> Real
  | Integer, Num | Num, Integer -> Num
  | Vector (t1', _), Vector(t2', _) -> join_types t1' t2'
  | Bottom, t | t, Bottom -> t
  | _, _ ->
    failontype (Format.fprintf Format.str_formatter
                  "Cannot join these types %a %a" pp_typ t1 pp_typ t2;
                Format.flush_str_formatter () )


let rec res_type t =
  match t with
  | Function (t, t') -> t'
  | _ -> t

let array_type t =
  match t with
  | Vector (t, _) -> t
  | _ -> failontype "Array type must be applied to array types."

let is_array_type t =
  match t with
  | Vector (t,_) -> true
  | Bitvector _ -> true
  | _ -> false

let is_matrix_type t =
  match t with
  | Vector (Vector (t, _), _) -> true
  | _ -> false

let matrix_type t =
  match t with
  | Vector (Vector (t, _), _) -> t
  | _ -> failontype "Cannot extract matrix type, this is not a matrix."

let is_record_type t =
  match t with
  | Record _ -> true
  | _ -> false


(* -------------------- 2 - VARIABLES MANAGEMENT -------------------- *)

let _GLOB_VARIDS = ref 3000
let _new_id () = incr _GLOB_VARIDS; !_GLOB_VARIDS


module FnVs =
  Set.Make
    (struct
      type t = fnV
      let compare  x y = Pervasives.compare x.vid y.vid
    end)

module VarSet =
struct
  include FnVs
  let find_by_id vs id : FnVs.elt =
    FnVs.max_elt (FnVs.filter (fun elt -> elt.vid = id) vs)
  let find_by_name vs name : FnVs.elt =
    FnVs.max_elt (FnVs.filter (fun elt -> elt.vname = name) vs)
  let vids_of_vs vs : int list =
    List.map (fun vi -> vi.vid) (FnVs.elements vs)
  let has_vid vs id : bool =
    List.mem id (vids_of_vs vs)
  let bindings vs =
    List.map (fun elt -> (elt.vid, elt)) (FnVs.elements vs)
  let names vs =
    List.map (fun elt -> elt.vname) (FnVs.elements vs)
  let types vs =
    List.map (fun elt -> elt.vtype) (FnVs.elements vs)
  let record vs =
    List.map (fun elt -> elt.vname, elt.vtype) (FnVs.elements vs)
  let add_prefix vs prefix =
    FnVs.of_list (List.map (fun v -> {v with vname = prefix^v.vname}) (FnVs.elements vs))
  let iset vs ilist =
    FnVs.of_list
      (List.filter (fun vi -> List.mem vi.vid ilist) (FnVs.elements vs))
  let pp_var_names fmt vs =
    pp_print_list
      ~pp_sep:(fun fmt () -> fprintf fmt ", ")
      (fun fmt elt -> fprintf fmt "%s" elt.vname)
      fmt (FnVs.elements vs)
  let pp_vs fmt vs =
    fprintf fmt "@[<v 2>%a@]"
      (PpTools.pp_break_sep_list
         (fun fmt var -> printf "(%i: %s)" var.vid var.vname))
      (FnVs.elements vs)
end



type jcompletion = { cvi : fnV; cleft : bool; cright : bool; crec : bool }

module CSet = Set.Make (struct
    type t = jcompletion
    let compare jcs0 jcs1  =
      if jcs0.cvi.vid = jcs1.cvi.vid then
        (match jcs0.cleft && jcs0.cright, jcs1.cleft && jcs1.cright with
         | true, true -> 0
         | true, false -> 1
         | false, true -> -1
         | false, false -> if jcs0.cleft then 1 else -1)
      else Pervasives.compare jcs0.cvi.vid jcs1.cvi.vid
  end)

(* Completions set: used in holes to express the set of possible expressions
   or variables to use. *)
module CS = struct
  include CSet
  let of_vs vs =
    VarSet.fold
      (fun vi cset -> CSet.add {cvi = vi; cleft = false; cright = false; crec = false} cset)
      vs CSet.empty


  let map f cs =
    CSet.fold (fun jc cset -> CSet.add (f jc) cset)
      cs CSet.empty


  let _L cs =
    CSet.fold (fun jc cset -> CSet.add {jc with cleft = true} cset)
      cs CSet.empty

  let _R cs =
    CSet.fold (fun jc cset -> CSet.add {jc with cright = true} cset)
      cs CSet.empty

  let _LorR cs =
    map (fun jc -> {jc with cleft = true; cright = true;}) cs

  let _LRorRec ?(filt=(fun i -> true)) cs =
    map (fun jc -> {jc with cleft = true; cright = true; crec = true;})
      (CSet.filter filt cs)

  let to_jc_list cs =
    CSet.fold (fun jc jclist -> jc::jclist)
      cs []

  let to_vs cs =
    CSet.fold (fun jc vs -> VarSet.add jc.cvi vs) cs VarSet.empty

  let pp_cs index_string fmt cs =
    let lprefix = Conf.get_conf_string "rosette_join_left_state_prefix" in
    let rprefix = Conf.get_conf_string "rosette_join_right_state_prefix" in
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@;")
      (fun fmt jc ->
         match jc.cvi.vtype with
         | Vector _ ->
           begin match jc.cleft, jc.cright, jc.crec with
             | true, false, false ->
               fprintf fmt "(list-ref %s%s %s)" lprefix jc.cvi.vname index_string;
             | false, true, false ->
               fprintf fmt "(list-ref %s%s %s)" rprefix jc.cvi.vname index_string;
             | true, true, false ->
               fprintf fmt "(list-ref %s%s %s)@;(list-ref %s%s %s)"
                 lprefix jc.cvi.vname index_string
                 rprefix jc.cvi.vname index_string;
             | false, true, true ->
               fprintf fmt "(list-ref %s %s)@;(list-ref %s%s %s)"
                 jc.cvi.vname index_string
                 rprefix jc.cvi.vname index_string;
             | true, true, true ->
               fprintf fmt "(list-ref %s %s)@;(list-ref %s%s %s)@;(list-ref %s%s %s)"
                 jc.cvi.vname index_string
                 rprefix jc.cvi.vname index_string
                 lprefix jc.cvi.vname index_string;

             | _ -> failhere __FILE__ "pp_cs" "Unexpected completion directive."
           end


         | _ ->
           begin match jc.cleft, jc.cright, jc.crec with
             | true, false, false ->
               fprintf fmt "%s%s" lprefix jc.cvi.vname;
             | false, true, false ->
               fprintf fmt "%s%s" rprefix jc.cvi.vname;
             | true, true, false ->
               fprintf fmt "%s%s@;%s%s"
                 lprefix jc.cvi.vname rprefix jc.cvi.vname;
             | false, true, true ->
               fprintf fmt "%s@;%s%s"
                 jc.cvi.vname rprefix jc.cvi.vname;
             | true, true, true ->
               fprintf fmt "%s@;%s%s@;%s%s"
                 jc.cvi.vname rprefix jc.cvi.vname lprefix jc.cvi.vname;

             | _ -> failhere __FILE__ "pp_cs" "Unexpected completion directive."
           end)
      fmt (to_jc_list cs)
end


(* -------------------- 3 - GENERAL VARIABLE NAMES -------------------- *)

(* General variable name generation. Can contain associated varinfo / fnV *)
let _VARS = SH.create 10
let register s =
  SH.add _VARS s [(_new_id (), None, None)]

let has_l_id l id =
  List.exists (fun (i, _, _) -> i = id) l

let register_vi (vi : Cil.varinfo) =
  if SH.mem _VARS vi.Cil.vname then
    let vars = SH.find _VARS vi.Cil.vname in
    SH.replace _VARS vi.Cil.vname
      (if has_l_id vars vi.Cil.vid then
         (List.map
            (fun (i, ovar, ovi) ->
               if i = vi.Cil.vid then
                 (i, ovar, Some vi)
               else
                 (i, ovar, ovi)) vars)
       else
         vars@[(vi.Cil.vid, None, Some vi)])
  else
    SH.add _VARS vi.Cil.vname [(vi.Cil.vid, None, Some vi)]

let register_vs (vs : VS.t) = VS.iter register_vi vs

let register_fnv (var : fnV) =
  if SH.mem _VARS var.vname then
    let vars = SH.find _VARS var.vname in
    SH.replace _VARS var.vname
      (if has_l_id vars var.vid then
         (List.map
            (fun (i, ovar, ovi) ->
               if i = var.vid then
                 (i, Some var, ovi)
               else
                 (i, ovar, ovi)) vars)
       else
         vars@[(var.vid, Some var, None)])
  else
    SH.add _VARS var.vname [(var.vid, Some var, None)]

let register_varset (vs : VarSet.t) = VarSet.iter register_fnv vs

let new_name_counter = ref 0

let get_new_name ?(base = "x") =
  if SH.mem _VARS base then
    let rec create_new_name x =
      let try_name = base^(string_of_int !new_name_counter) in
      incr new_name_counter;
      if SH.mem _VARS try_name then
        create_new_name base
      else
        try_name
    in
    create_new_name base
  else
    base

let find_var_name name =
  match snd3 (List.hd (SH.find _VARS name)) with
  | Some var -> var
  | None -> raise Not_found

let find_vi_name name =
  match third (List.hd (SH.find _VARS name)) with
  | Some vi -> vi
  | None -> raise Not_found

let find_vi_name_id name id =
  let vlist = SH.find _VARS name in
  match third (List.find (fun (i, _, _) -> i = id) vlist) with
  | Some vi -> vi
  | None -> raise Not_found

let find_var_name_id name id =
  let vlist = SH.find _VARS name in
  match snd3 (List.find (fun (i, _, _) -> i = id) vlist) with
  | Some var -> var
  | None -> raise Not_found

let mkFnVar name typ =
  let var_name = get_new_name ~base:name in
  let var =
    { vname = var_name;
      vtype = typ;
      vid = _new_id ();
      vistmp = false;
      vinit = None;}
  in
  register_fnv var;
  var

let special_binder typ =
  let vname = "type_"^shstr_of_type typ in
  try
    find_var_name vname
  with Not_found ->
    mkFnVar vname typ



(* -------------------- 4 - LEFT AND RIGHT STATE VARIABLES ------------------ *)

let rhs_prefix = (Conf.get_conf_string "rosette_join_right_state_prefix")
let lhs_prefix = (Conf.get_conf_string "rosette_join_left_state_prefix")

let is_side_state_varname s side_prefix =
  let varname_parts = Str.split (Str.regexp "\.") s in
  let side_state_name = (Str.split (Str.regexp "\.") side_prefix) >> 0 in
  match List.length varname_parts with
  | 2 -> varname_parts >> 1, true, (varname_parts >> 0) = side_state_name
  | 1 -> varname_parts >> 0, false, false
  | _ ->
    failwith (fprintf str_formatter
                "Unexpected list length when splitting variable name %s \
                 over '.'" s; flush_str_formatter ())

let is_left_state_varname s = is_side_state_varname s lhs_prefix
let is_right_state_varname s = is_side_state_varname s rhs_prefix

(* -------------------- 5 - INDEXES -------------------- *)

let start_iname = Conf.get_conf_string "rosette_index_suffix_start"
let end_iname = Conf.get_conf_string "rosette_index_suffix_end"

let index_to_boundary : (fnV * fnV) IH.t = IH.create 10



let create_boundary_variables index_set =
  VarSet.iter
    (fun index_vi ->
       let starti =
         mkFnVar (index_vi.vname^start_iname) index_vi.vtype
       in
       let endi =
         mkFnVar (index_vi.vname^end_iname) index_vi.vtype
       in
       IH.add index_to_boundary index_vi.vid (starti, endi))
    index_set

let get_index_to_boundary vi =
  IH.find index_to_boundary vi.vid

let left_index_vi vi =
  if IH.length index_to_boundary = 0 then failwith "Empty index!" else ();
  let l, _ = get_index_to_boundary vi in l

let is_left_index_vi i =
  try
    (IH.iter
       (fun vid (vil, _) ->
          if i = vil then failwith "found" else ()) index_to_boundary;
     false)
  with Failure s -> if s = "found" then true else false

let right_index_vi vi =
  if IH.length index_to_boundary = 0 then failwith "Empty index!" else ();
  let _, r = IH.find index_to_boundary vi.vid in r

let is_right_index_vi i =
  try
    (IH.iter
       (fun vid (_, vir) ->
          if i = vir then failwith "found" else ()) index_to_boundary;
     false)
  with Failure s -> if s = "found" then true else false



(* -------------------- 6 - AUXILIARY VARIABLES -------------------- *)


let aux_vars : fnV IH.t = IH.create 10

let concretize_aux fc =
  IH.fold fc aux_vars


let cur_left_auxiliaries = ref VarSet.empty
let cur_right_auxiliaries = ref VarSet.empty

let left_aux_ids : int list ref = ref []
let right_aux_ids : int list ref = ref []

let add_laux_id i = left_aux_ids := i :: !left_aux_ids
let add_raux_id i = right_aux_ids := i :: !right_aux_ids

let add_left_auxiliary vi =
  add_laux_id vi.vid;
  cur_left_auxiliaries:=
    (VarSet.add vi !cur_left_auxiliaries)

let add_right_auxiliary vi =
  add_raux_id vi.vid;
  cur_right_auxiliaries:=
    (VarSet.add vi !cur_right_auxiliaries)

let is_left_aux_id i = List.mem i !left_aux_ids
let is_left_aux var = VarSet.mem var !cur_left_auxiliaries

let is_right_aux_id i = List.mem i !right_aux_ids
let is_right_aux var = VarSet.mem var !cur_right_auxiliaries

let aux_vars_init () =
  IH.clear aux_vars;
  cur_left_auxiliaries := VarSet.empty;
  cur_right_auxiliaries := VarSet.empty

let is_currently_aux vi : bool = IH.mem aux_vars vi.vid

(* Variable discovery: new variables *)
let d_aux_alltime : fnV IH.t = IH.create 10
let d_aux : fnV IH.t = IH.create 10

let copy_aux_to dest =
  IH.copy_into d_aux_alltime dest

let discover_init () =
  IHTools.add_all d_aux_alltime d_aux;
  IH.clear d_aux

let discover_clear () =
  IH.clear d_aux;
  IH.clear d_aux_alltime

let discover_add v =
  IH.add d_aux v.vid v

let discover_save () =
  IH.copy_into d_aux_alltime aux_vars

(* ----------------- 7 - NESTED LOOPS : OUTER STATE VARIABLES --------------- *)

let outer_used = IH.create 10

let outer_marked_clear () =
  IH.clear outer_used

let mark_outer_used fnv : unit =
  IH.add outer_used fnv.vid true

let is_outer_used fnv : bool =
  IH.mem outer_used fnv.vid


(* -------------------- 8 - RECORDS -------------------- *)


(* Managing tuple or record types. *)
let rosette_prefix_struct = Conf.get_conf_string "rosette_struct_name"
let declared_tuple_types = SH.create 10

let rec record_name
    ?(only_by_type=false) ?(seed = "") (vs : VarSet.t) : string =
  let stl = VarSet.record vs in
  let tl = (ListTools.unpair --> snd) stl in
  let poten_name =
    String.concat seed ([rosette_prefix_struct]@(List.map shstr_of_type tl))
  in
  if only_by_type then
    poten_name
  else if SH.mem declared_tuple_types poten_name then
    let stl', vs' = SH.find declared_tuple_types poten_name in
    if VarSet.equal vs vs' then poten_name
    else
      record_name ~seed:(seed^"_") vs
  else
    (SH.add declared_tuple_types poten_name (stl, vs);
     poten_name)

let record_type (vs : VarSet.t) : fn_type =
  let tl = VarSet.record vs in
  let name = record_name vs in
  Record(name, tl)

let is_name_of_struct s =
  SH.mem declared_tuple_types s

let get_struct s =
  SH.find declared_tuple_types s

let record_accessor s v =
  {
    vname = s^"-"^v.vname;
    vtype = v.vtype;
    vid = _new_id ();
    vinit = None;
    vistmp = true;
  }

let is_struct_accessor a =
  try
    let parts = Str.split (Str.regexp "-") a in
    List.length parts = 2 &&
    str_begins_with rosette_prefix_struct (parts >> 0)
  with
  | Not_found -> false
  | Invalid_argument s -> false

let record_map vs f =
  IM.mapi (fun i e -> let var = VarSet.find_by_id vs i in f var e)
