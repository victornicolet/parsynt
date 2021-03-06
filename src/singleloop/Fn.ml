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

open Beta
open Utils
open ListTools
open Format
open Lang

(* open Loops *)
open Sygus
open Sygus.Synthlib2ast

(*
   1 - Expressions.
   2 - Basic helper functions.
   3 - Typing functions.
   4 - Recursors.
   5 - Scheme & func transformers.
   6 - Expression sets.
   7 - Index variables management (expressions part)
   8 - Structs for problem info.
   9 - Conversion to CIL.
*)

let use_unsafe_operations = ref false

let rosette_prefix_struct = Naming.Rosette.struct_name

let debug = ref false

(* ---------------------------- 1 - EXPRESSIONS ----------------------------- *)

type hole_type = fn_type * operator_type

(* Type for variables *)
and fnLVar =
  | FnVariable of fnV
  (* Access to an array cell *)
  | FnArray of fnLVar * fnExpr

(* Type for expressions *)
and fnExpr =
  | FnLetIn of (fnLVar * fnExpr) list * fnExpr
  | FnVar of fnLVar
  | FnConst of constants
  | FnFun of fnExpr
  | FnRec of (fnExpr * fnExpr * fnExpr) * (VarSet.t * fnExpr) * (fnV * fnExpr)
  | FnCond of fnExpr * fnExpr * fnExpr
  | FnBinop of symb_binop * fnExpr * fnExpr
  | FnUnop of symb_unop * fnExpr
  | FnApp of fn_type * fnV option * fnExpr list
  | FnHoleL of hole_type * fnLVar * CS.t * fnExpr * int
  | FnHoleR of hole_type * CS.t * fnExpr * int
  | FnChoice of fnExpr list
  | FnVector of fnExpr list
  | FnArraySet of fnExpr * fnExpr * fnExpr
  | FnRecord of VarSet.t * fnExpr IM.t
  | FnRecordMember of fnExpr * string
  (* Simple translation of Cil exp needed to nest
      sub-expressions with state variables *)
  | FnSizeof of fn_type
  | FnSizeofE of fnExpr
  | FnSizeofStr of string
  | FnAlignof of fn_type
  | FnAlignofE of fnExpr
  | FnCastE of fn_type * fnExpr
  | FnAddrof of fnExpr
  | FnStartOf of fnExpr

and fnDefinition = fnV * fnV list * fnExpr

(** Get the varinfo of a variable. *)
let rec vi_of fnlv =
  match fnlv with FnVariable vi' -> Some vi' | FnArray (fnlv', _) -> vi_of fnlv'

(* -------------------- 2 - TYPING FUNCTIONS -------------------- *)

let type_of_unop (t : fn_type) : symb_unop -> fn_type option =
  let type_of_unsafe_unop _ = function _ -> Real in
  function
  | Not -> if t = Boolean then Some Boolean else None
  | Neg | Abs | Add1 | Sub1 -> if is_subtype t Real then Some t else None
  | Floor | Ceiling | Round | Truncate -> if is_subtype t Real then Some Integer else None
  | Sgn -> if is_subtype t Real then Some Boolean else None
  | UnsafeUnop op -> Some (type_of_unsafe_unop t op)

let type_of_binop t1 t2 : symb_binop -> fn_type option =
  let join_t = join_types t1 t2 in
  let type_of_unsafe_binop _t1 _t2 = function _ -> Some Real in
  function
  | And | Nand | Xor | Or | Implies | Nor ->
      if is_subtype join_t Boolean then Some Boolean else None
  | Le | Ge | Gt | Lt | Neq -> if is_subtype join_t Real then Some Boolean else None
  | Eq -> Some Boolean
  | Plus | Minus | Times | Div | Rem | Quot | Expt | Mod | Max | Min ->
      if is_subtype join_t Real then Some join_t else None
  | UnsafeBinop o -> type_of_unsafe_binop t1 t2 o
  | ShiftL | ShiftR -> Some (Bitvector 0)

let rec type_of_const c =
  match c with
  | CNil -> Unit
  | CBool _ -> Boolean
  | CChar _ -> Integer
  | CString _ -> List (Integer, None)
  | CArrayInit (_, c) -> type_of_const c
  | CReal _ -> Real
  | CInt _ | CInt64 _ -> Integer
  | CBox b -> Box (type_of_cilconst b)
  | CUnop (op, c) -> type_of (FnUnop (op, FnConst c))
  | CBinop (op, c, c') -> type_of (FnBinop (op, FnConst c, FnConst c'))
  | Pi | SqrtPi | Sqrt2 | E | Ln2 | Ln10 -> Real
  | CUnsafeBinop (_, c, c') -> join_types (type_of_const c) (type_of_const c')
  | CUnsafeUnop (_, c) -> type_of_const c
  | Infnty | NInfnty -> Num

and type_of_var v =
  match v with
  | FnVariable vi -> vi.vtype
  | FnArray (v, _) -> (
      (* We only consider integer indexes for now.
         Return the type of the array cells *)
      match type_of_var v with
      | Vector (tv, _) -> tv
      | t ->
          failwith
            (Format.fprintf Format.str_formatter "Unexpected type %a for variable in array access."
               pp_typ t;
             Format.flush_str_formatter ()))

and type_of expr =
  match expr with
  | FnVar v -> type_of_var v
  | FnRecord (vs, _) ->
      let stl = VarSet.record vs in
      Record (record_name vs, stl)
  | FnConst c -> type_of_const c
  | FnStartOf _ | FnSizeof _ | FnSizeofE _ | FnSizeofStr _ | FnAlignof _ | FnAlignofE _ | FnAddrof _
    ->
      Integer
  | FnCastE (t, _) -> t
  | FnUnop (unop, e) -> (
      match type_of_unop (type_of e) unop with
      | Some x -> x
      | None -> failwith "Could not find type of expressions.")
  | FnBinop (binop, e1, e2) -> (
      match type_of_binop (type_of e1) (type_of e2) binop with
      | Some x -> x
      | None -> failwith "Could not find type of expressions.")
  | FnCond (_, e1, e2) -> join_types (type_of e1) (type_of e2)
  | FnApp (t, _, _) -> t
  | FnHoleL (ht, _, _, _, _) | FnHoleR (ht, _, _, _) -> ( match ht with t, _ -> t)
  | FnFun e -> Function (type_of e, type_of e)
  | FnVector a -> Vector (type_of (List.nth a 0), Some (List.length a))
  | FnRecordMember (e, _) -> (
      match type_of e with
      | Record (s, stl) -> (
          try
            let _, t0 = List.hd (List.filter (fun (s', _) -> s = s') stl) in
            t0
          with _ -> failontype "Record member not found in record type.")
      | _ -> failontype "Should be a record type inside a record mmeber access.")
  | FnLetIn (_, e) -> type_of e
  | FnChoice _ -> Bottom
  | FnArraySet (a, _, _) -> type_of a
  | FnRec (_, _, (s, _)) -> s.vtype

let filter_vs_by_type t = VarSet.filter (fun vi -> vi.vtype = t)

let filter_cs_by_type t =
  CS.filter (fun jc -> match jc.cvi.vtype with Vector (st, _) -> st = t | st -> st = t)

let rec input_type_or_type = function Function (it, _) -> input_type_or_type it | t -> t

(** ----------------------- 3 - BASIC HELPER FUNCTIONS -----------------------*)

(* Given a cil operator, return an unary symb operator and a type *)
let symb_unop_of_cil : Term.Unop.t -> symb_unop * fn_type = function
  | Not -> (Not, Boolean)
  | Neg -> (Neg, Num)
  | Abs -> (Abs, Num)
  | _ -> failwith "operator not supported."

(* Given a cil operator, return a binary symb operator and a type *)
let symb_binop_of_cil : Term.Binop.t -> symb_binop * fn_type = function
  | Plus -> (Plus, Num)
  | Minus -> (Minus, Num)
  | Times -> (Times, Num)
  | Div -> (Div, Num)
  | Mod -> (Mod, Integer)
  | Or -> (Or, Boolean)
  | And -> (Or, Boolean)
  | Max -> (Max, Integer)
  | Min -> (Min, Integer)
  | Lt -> (Lt, Num)
  | Le -> (Le, Num)
  | Gt -> (Gt, Num)
  | Ge -> (Ge, Num)
  | Eq -> (Eq, Num)
  | _ -> failwith "Operator not supported."

(* Return the type associated to a binary operator. *)
let optype_of_binop = function
  | Expt | Times | Div -> NonLinear
  | Max | Min -> Basic
  | Plus | Minus -> Arith
  | _ -> NotNum

(* Return the type associated to a unary operator. *)
let optype_of_unop = function
  | Truncate | Round | UnsafeUnop _ | Abs | Floor | Ceiling -> NonLinear
  | Add1 | Sub1 | Neg -> Arith
  | Sgn | Not -> NotNum

(* Join two operator types. Numeral operator types can be ordered,
   Basic < Arith < NonLinear
*)
let join_optypes opt1 opt2 =
  match (opt1, opt2) with
  | NonLinear, _ | _, NonLinear -> NonLinear
  | Basic, _ | _, Basic -> Basic
  | Arith, _ | _, Arith -> Arith
  | _, _ -> NotNum
(* Join *)

(* The identity function in the functional representation of the func. *)
let identity_fn = FnRecord (VarSet.empty, IM.empty)

let identity_map vs =
  VarSet.fold (fun var emap -> IM.set var.vid (FnVar (FnVariable var)) emap) vs IM.empty

(* Translate C Standard Library function names in
    functions supported by Rosette
*)
let symb_unop_of_fname = function
  | "floor" | "floorf" | "floorl" -> Some Floor
  | "abs" | "fabs" | "fabsf" | "fabsl" | "labs" | "llabs" | "imaxabs" -> Some Abs
  | "ceil" -> Some Ceiling
  (* C++11 *)
  | "trunc" | "truncf" | "truncl" -> Some Truncate
  | "lround" | "lroundf" | "lroundl" | "round" | "roundf" | "roundl" | "nearbyint" | "nearbyintf"
  | "nearbyintl" | "llround" | "llroundf" | "llroundl" | "rint" | "rintf" | "rintl" ->
      Some Round
  | "sub1" -> Some Sub1
  | "add1" -> Some Add1
  | _ -> None

let symb_binop_of_fname : string -> symb_binop option = function
  | "modf" | "modff" | "modfl" -> Some Mod
  | "fmod" | "fmodl" | "fmodf" -> Some Mod
  | "remainder" | "remainderf" | "remainderl" | "drem" | "dremf" | "dreml" -> Some Rem
  | "max" | "fmax" | "fmaxf" | "fmaxl" -> Some Max
  | "min" | "fmin" | "fminf" | "fminl" -> Some Min
  (*
      Comparison macros/functions in C++11
      /!\ Unsafe
  *)
  | "isgreater" -> Some Gt
  | "isgreaterequal" -> Some Ge
  | "isless" -> Some Lt
  | "islessequal" -> Some Le
  | "islessgreater" -> Some Neq
  | "isunordered" -> Some Neq
  | _ -> None

(* Some operators are unsafe to use in Rosette. *)
let unsafe_unops_of_fname = function
  | "sin" -> Some Sin
  | "cos" -> Some Cos
  | "tan" -> Some Tan
  | "asin" -> Some ASin
  | "acos" -> Some ACos
  | "atan" -> Some ATan
  | "exp" -> Some Exp
  | "log" -> Some Log
  | "log10" -> Some Log10
  | "log2" -> Some Log2
  | "sqrt" -> Some Sqrt
  | _ -> None

let unsafe_binops_of_fname = function _ -> None

let is_comparison_op : symb_binop -> bool = function Eq | Gt | Lt | Le | Ge -> true | _ -> false
(*
    Mathematical constants defined in GNU-GCC math.h.
   + other custom constants defined in the decl_header.c

    TODO : integrate log/ln/pow function, not in
    rosette/safe AFAIK.
*)

(* Some predefined constatns in C can be translated to expressions
   in the func functional represenation.out_newline.
*)

let c_constant ccst =
  match ccst with
  | s when Config.is_builtin_var s -> (
      match Config.get_builtin s with
      | Config.Max_Int -> Some Infnty
      | Config.Min_Int -> Some NInfnty
      | Config.True -> Some (CBool true)
      | Config.False -> Some (CBool false))
  | "M_E" -> Some E
  | "M_LN2" -> Some Ln2
  | "M_LN10" -> Some Ln10
  | "M_PI" -> Some Pi
  | "M_PI_2" -> Some (CBinop (Div, Pi, CInt 2))
  | "M_PI_4" -> Some (CBinop (Div, Pi, CInt 2))
  | "M_1_PI" -> Some (CBinop (Div, CReal 1.0, Pi))
  | "M_2_PI" -> Some (CBinop (Div, CReal 2.0, Pi))
  | _ ->
      if !use_unsafe_operations then
        match ccst with
        | "M_SQRT2" -> Some Sqrt2
        | "M_SQRT1_2" -> Some (CBinop (Div, CReal 1.0, Sqrt2))
        | "M_2_SQRTPI" -> Some (CBinop (Div, CReal 2.0, SqrtPi))
        | "M_LOG10E" -> Some (CBinop (Div, CReal 1.0, Ln10))
        | "M_LOG2E" -> Some (CBinop (Div, CReal 1.0, Ln2))
        | _ -> None
      else None

(* Returns true if a constant is negative. *)
let is_negative cst =
  match cst with CInt i -> i < 0 | CInt64 i -> i < 0L | CReal f -> f < 0.0 | _ -> false

(**
    A function name not appearing in the cases above
    will be treated as an "uninterpreted function" by
    default.
*)

let uninterpeted fname =
  let not_in_safe =
    match symb_unop_of_fname fname with
    | Some _ -> false
    | None -> (
        match symb_binop_of_fname fname with
        | Some _ -> false
        | None -> ( match c_constant fname with Some _ -> false | None -> true))
  in
  let not_in_unsafe =
    if !use_unsafe_operations then
      match unsafe_unops_of_fname fname with Some _ -> false | None -> true
    else true
  in
  not_in_safe && not_in_unsafe

(* Remove interpreted symbols, i.e remove the variables
   that have a name that is a function.
*)
let remove_interpreted_symbols (vars : VarSet.t) =
  VarSet.filter (fun v -> uninterpeted v.vname) vars

let fn_zero = FnConst (CInt 0)

(**
   Generate a FnVar expression from a variable, with possible offsets
   for arrays. Checks first if the name of the variable is a predefined
   constant.
*)
let mkVar ?(offsets = []) vi =
  List.fold_left (fun fnlvar offset -> FnArray (fnlvar, offset)) (FnVariable vi) offsets

(**
   Create an expression from a varinfo and offsets, possibly returning
   a constant if the name of the variable is a predefined constant.
*)
let mkVarExpr ?(offsets = []) vi =
  match c_constant vi.vname with Some c -> FnConst c | None -> FnVar (mkVar ~offsets vi)

let rec var_of_fnvar (fnvar : fnLVar) : fnV =
  match fnvar with FnVariable v -> v | FnArray (v, _) -> var_of_fnvar v

let empty_record : fnExpr = FnRecord (VarSet.empty, IM.empty)

let is_empty_record (expr : fnExpr) : bool =
  match expr with FnRecord (vs, im) -> VarSet.is_empty vs && IM.is_empty im | _ -> false

let bind_state ?(prefix = "") ~state_rec:state_var vs =
  let vars = VarSet.elements vs in
  List.map
    (fun v ->
      (FnVariable { v with vname = prefix ^ v.vname }, FnRecordMember (mkVarExpr state_var, v.vname)))
    vars

let unwrap_state (vs : VarSet.t) (emap : fnExpr IM.t) : (fnLVar * fnExpr) list =
  VarSet.fold
    (fun var bindings ->
      let expr = IM.find var.vid emap in
      bindings @ [ (FnVariable var, expr) ])
    vs []

let wrap_state (bindings : (fnLVar * fnExpr) list) : fnExpr =
  let rec rewrap_binding (lvar, e) =
    match lvar with
    | FnVariable var -> (var, e)
    | FnArray (lvar, i) -> rewrap_binding (lvar, FnArraySet (FnVar lvar, i, e))
  in
  let vl = List.map rewrap_binding bindings in
  let vs = VarSet.of_list (fst (Base.List.unzip vl)) in
  let emap = List.fold_left (fun emap (v, e) -> IM.set v.vid e emap) IM.empty vl in
  FnRecord (vs, emap)

let flat_bindings (func : fnExpr) : (fnLVar * fnExpr) list =
  let rec aux e l =
    match e with
    | FnLetIn (l', e') -> aux e' (l @ l')
    | FnRecord (vs, emap) -> l @ unwrap_state vs emap
    | _ -> l
  in
  aux func []

let all_record_accessors (l : (fnLVar * fnExpr) list) : fnV option =
  if
    List.length l > 0
    && List.for_all (fun (_, e) -> match e with FnRecordMember (_, _) -> true | _ -> false) l
  then match List.hd l with _, FnRecordMember (FnVar (FnVariable var), _) -> Some var | _ -> None
  else None

let is_vi fnlv vi = maybe_apply_default (fun x -> vi = x) (vi_of fnlv) false

let is_reserved_name s = not (uninterpeted s)

(** Get the dependency length of an array variable. We assume very
    simple offset expressions.*)

let rec fnArray_dep_len e =
  match e with
  | FnVar v -> ( match v with FnVariable _ -> 1 | FnArray (_, e') -> fnArray_dep_len e')
  | FnConst (CInt i) -> i + 1
  | FnConst (CInt64 i) -> Int64.to_int i + 1
  | FnBinop (op, e1, e2) when op = Plus || op = Minus -> fnArray_dep_len e1 + fnArray_dep_len e2
  | _ ->
      eprintf "ERROR : cannot guess min array length of expression.@.";
      failwith "Unsupported array offset expression."

(** Remove interpreted symbols from a set of vars *)
let remove_reserved_vars (vs : Term.VarSet.t) : Term.VarSet.t =
  Base.Set.filter
    ~f:(fun vi ->
      if uninterpeted vi.vname then (
        if !debug then printf "@.Removing %s." vi.vname;
        true)
      else false)
    vs

(** When an expression is supposed to be a constant *)
let force_constant expr = match expr with FnConst c -> c | _ -> failwith "Force_constant failure."

let mkOp ?(t = Unit) vi argl =
  let fname = vi.vname in
  match symb_unop_of_fname fname with
  | Some unop -> FnUnop (unop, List.hd argl)
  | None -> (
      match symb_binop_of_fname fname with
      | Some binop -> FnBinop (binop, List.hd argl, List.nth argl 2)
      | None -> FnApp (t, Some vi, argl))

(* Convert Cil Varinfo to variable *)

let var_of_vi (vi : Typ.variable) =
  let var =
    {
      vname = vi.vname;
      vinit = None;
      vtype = type_of_ciltyp vi.vtype;
      vid = vi.vid;
      vistmp = false;
    }
  in
  register_fnv var;
  var

let variable_of_vi (vi : fnV) : Typ.variable =
  match ciltyp_of_symb_type vi.vtype with
  | Some t -> Typ.{ vname = vi.vname; vtype = t; vid = vi.vid; vattrs = [] }
  | None -> failwith "Unexpected"

let varset_of_vs (vs : Term.VarSet.t) = VarSet.of_list (List.map var_of_vi (Base.Set.elements vs))

(* Compare variables by comparing the variable id of their varinfo. *)
let rec cmpVar fnlvar1 fnlvar2 =
  match (fnlvar1, fnlvar2) with
  | FnVariable vi, FnVariable vi' -> compare vi.vid vi'.vid
  | FnArray (fnlv1, _), FnArray (fnlv2, _) -> cmpVar fnlv1 fnlv2
  | FnArray _, _ -> 1
  | _, FnArray _ -> -1

(* ---------------------------- 4 - RECURSORS -------------------------------*)

type 'a recursor = {
  join : 'a -> 'a -> 'a;
  init : 'a;
  case : fnExpr -> bool;
  on_case : (fnExpr -> 'a) -> fnExpr -> 'a;
  on_const : constants -> 'a;
  on_var : fnLVar -> 'a;
}

(** Helper for recursion in expressions
    @param join join two return values, the join operation must be associtaive
    to avoid unexpected behaviour.
    @param init an identity value for the return value
    @param const_handler return a value for constants
    @param var_handler returns a vlaue for variables
    @param expre the input expression to apply the recursion on.
    @return a return value obtained by recusrively joining the values
    depending on the values in the leaves.
*)
let rec_expr (join : 'a -> 'a -> 'a) (init : 'a) (case : fnExpr -> bool)
    (case_handler : (fnExpr -> 'a) -> fnExpr -> 'a) (const_handler : constants -> 'a)
    (var_handler : fnLVar -> 'a) (expre : fnExpr) : 'a =
  let rec recurse_aux = function
    | e when case e -> case_handler recurse_aux e
    | FnVar v -> var_handler v
    | FnConst c -> const_handler c
    | FnVector el -> List.fold_left (fun a e -> join a (recurse_aux e)) init el
    | FnBinop (_, e1, e2) -> join (recurse_aux e1) (recurse_aux e2)
    | FnCastE (_, e) | FnAlignofE e | FnAddrof e | FnSizeofE e | FnStartOf e | FnUnop (_, e) ->
        recurse_aux e
    | FnCond (c, e1, e2) -> join (join (recurse_aux c) (recurse_aux e1)) (recurse_aux e2)
    | FnApp (_, _, el) -> List.fold_left (fun a e -> join a (recurse_aux e)) init el
    | FnFun letin | FnRec (_, _, (_, letin)) -> recurse_aux letin
    | FnRecord (_, emap) -> IM.fold (fun _ e acc -> join acc (recurse_aux e)) emap init
    | FnLetIn (velist, letin) ->
        let in_aux = recurse_aux letin in
        List.fold_left (fun acc (_, e) -> join acc (recurse_aux e)) in_aux velist
    | _ -> init
  in
  recurse_aux expre

let rec_expr2 (r : 'a recursor) = rec_expr r.join r.init r.case r.on_case r.on_const r.on_var

let max_min_test =
  {
    join = (fun a b -> a || b);
    init = false;
    case = (fun e -> match e with FnBinop (op, _, _) -> op = Max || op = Min | _ -> false);
    on_case = (fun _ e -> match e with FnBinop (op, _, _) -> op = Max || op = Min | _ -> false);
    on_const = (fun _ -> false);
    on_var = (fun _ -> true);
  }

type ast_transformer = {
  case : fnExpr -> bool;
  on_case : (fnExpr -> fnExpr) -> fnExpr -> fnExpr;
  on_const : constants -> constants;
  on_var : fnLVar -> fnLVar;
}
(** Another recursion helper : a syntax tree tranformer *)

let transform_expr (case : fnExpr -> bool) (case_handler : (fnExpr -> fnExpr) -> fnExpr -> fnExpr)
    (const_handler : constants -> constants) (var_handler : fnLVar -> fnLVar) (expre : fnExpr) : 'a
    =
  let rec recurse_aux expr =
    match expr with
    | e when case e -> case_handler recurse_aux e
    | FnVar v -> FnVar (var_handler v)
    | FnConst c -> FnConst (const_handler c)
    | FnBinop (op, e1, e2) -> FnBinop (op, recurse_aux e1, recurse_aux e2)
    | FnUnop (op, e) -> FnUnop (op, recurse_aux e)
    | FnApp (a, b, el) -> FnApp (a, b, List.map (fun e -> recurse_aux e) el)
    | FnFun letin -> FnFun (recurse_aux letin)
    | FnRec ((i, g, u), (inner_state, init_inner_state), (s, letin)) ->
        FnRec
          ( (recurse_aux i, recurse_aux g, recurse_aux u),
            (inner_state, recurse_aux init_inner_state),
            (s, recurse_aux letin) )
    | FnCond (c, l1, l2) -> FnCond (recurse_aux c, recurse_aux l1, recurse_aux l2)
    | FnLetIn (velist, letin) ->
        let in_aux = recurse_aux letin in
        FnLetIn (List.map (fun (v, e) -> (v, recurse_aux e)) velist, in_aux)
    | FnHoleL (t, v, cs, e, d) -> FnHoleL (t, v, cs, recurse_aux e, d)
    | FnHoleR (t, cs, e, d) -> FnHoleR (t, cs, recurse_aux e, d)
    | FnChoice el -> FnChoice (List.map recurse_aux el)
    | FnVector ea -> FnVector (List.map recurse_aux ea)
    | FnRecord (t, el) -> FnRecord (t, IM.map recurse_aux el)
    | FnRecordMember (e, s) -> FnRecordMember (recurse_aux e, s)
    | FnArraySet (a, i, e) -> FnArraySet (recurse_aux a, recurse_aux i, recurse_aux e)
    | FnCastE (t, e) -> FnCastE (t, recurse_aux e)
    | FnAlignofE e -> FnAlignofE (recurse_aux e)
    | FnAddrof e -> FnAddrof (recurse_aux e)
    | FnSizeofE e -> FnSizeofE (recurse_aux e)
    | FnStartOf e -> FnStartOf (recurse_aux e)
    | FnSizeof _ | FnAlignof _ | FnSizeofStr _ -> expr
  in
  recurse_aux expre

let transform_expr2 tr = transform_expr tr.case tr.on_case tr.on_const tr.on_var

(** Transformation with extra boolean argument *)
let transform_expr_flag (top : bool) (case : bool -> fnExpr -> bool)
    (case_handler : bool -> (bool -> fnExpr -> fnExpr) -> fnExpr -> fnExpr)
    (const_handler : bool -> constants -> constants) (var_handler : bool -> fnLVar -> fnLVar)
    (expre : fnExpr) : 'a =
  let rec recurse_aux flag = function
    | e when case flag e -> case_handler flag recurse_aux e
    | FnVar v -> FnVar (var_handler flag v)
    | FnConst c -> FnConst (const_handler flag c)
    | FnBinop (op, e1, e2) -> FnBinop (op, recurse_aux flag e1, recurse_aux flag e2)
    | FnCastE (t, e) -> FnCastE (t, recurse_aux flag e)
    | FnAlignofE e -> FnAlignofE (recurse_aux flag e)
    | FnAddrof e -> FnAddrof (recurse_aux flag e)
    | FnSizeofE e -> FnSizeofE (recurse_aux flag e)
    | FnStartOf e -> FnStartOf (recurse_aux flag e)
    | FnUnop (op, e) -> FnUnop (op, recurse_aux flag e)
    | FnApp (a, b, el) -> FnApp (a, b, List.map (fun e -> recurse_aux flag e) el)
    | FnFun letin -> FnFun (recurse_aux flag letin)
    | FnRec (igu, istate, (s, letin)) -> FnRec (igu, istate, (s, recurse_aux flag letin))
    | FnCond (c, l1, l2) -> FnCond (recurse_aux flag c, recurse_aux flag l1, recurse_aux flag l2)
    | FnRecord (vs, emap) -> FnRecord (vs, IM.map (recurse_aux flag) emap)
    | FnLetIn (velist, letin) ->
        let in_aux = recurse_aux flag letin in
        FnLetIn (List.map (fun (v, e) -> (v, recurse_aux flag e)) velist, in_aux)
    | e -> e
  in
  recurse_aux top expre

type ast_var_transformer = {
  ctx : fnLVar ref;
  case : fnExpr -> bool;
  on_case : (fnExpr -> fnExpr) -> fnExpr -> fnExpr;
  on_const : constants -> constants;
  on_var : fnLVar -> fnLVar;
}

let transform_bindings (tr : ast_var_transformer) =
  let rec recurse_aux = function
    | e when tr.case e -> tr.on_case recurse_aux e
    | FnVar v -> FnVar (tr.on_var v)
    | FnRecordMember (rv, s) -> FnRecordMember (recurse_aux rv, s)
    | FnConst c -> FnConst (tr.on_const c)
    | FnBinop (op, e1, e2) -> FnBinop (op, recurse_aux e1, recurse_aux e2)
    | FnCastE (t, e) -> FnCastE (t, recurse_aux e)
    | FnAlignofE e -> FnAlignofE (recurse_aux e)
    | FnAddrof e -> FnAddrof (recurse_aux e)
    | FnSizeofE e -> FnSizeofE (recurse_aux e)
    | FnStartOf e -> FnStartOf (recurse_aux e)
    | FnUnop (op, e) -> FnUnop (op, recurse_aux e)
    | FnApp (a, b, el) -> FnApp (a, b, List.map (fun e -> recurse_aux e) el)
    | FnFun letin -> FnFun (recurse_aux letin)
    | FnRec (igu, (inner_state, init_inner_state), (s, letin)) ->
        FnRec (igu, (inner_state, recurse_aux init_inner_state), (s, recurse_aux letin))
    | FnCond (c, l1, l2) -> FnCond (recurse_aux c, recurse_aux l1, recurse_aux l2)
    | FnRecord (vs, emap) ->
        FnRecord
          ( vs,
            record_map vs
              (fun v e ->
                tr.ctx := FnVariable v;
                recurse_aux e)
              emap )
    | FnLetIn (velist, letin) ->
        let in_aux = recurse_aux letin in
        FnLetIn
          ( List.map
              (fun (v, e) ->
                tr.ctx := v;
                (v, recurse_aux e))
              velist,
            in_aux )
    | e -> e
  in
  recurse_aux

(** An application of a function transformer : replace
    expression to_replace by expression by.
*)
let rec replace_expression ?(in_subscripts = false) ~to_replace:tr ~by:b exp =
  let case e = e = tr in
  let case_handler _ _ = b in
  let const_handler c = c in
  let rec var_handler v =
    if in_subscripts then
      match v with
      | FnArray (v, e) ->
          FnArray (var_handler v, replace_expression ~in_subscripts:true ~to_replace:tr ~by:b e)
      | _ -> v
    else v
  in
  transform_expr case case_handler const_handler var_handler exp

let to_rec_completions e =
  transform_expr2
    {
      case = (fun e -> match e with FnHoleL _ | FnHoleR _ -> true | _ -> false);
      on_case =
        (fun f e ->
          match e with
          | FnHoleL (ht, var, cst, e', d) -> FnHoleL (ht, var, CS._LRorRec cst, e', d)
          | FnHoleR (ht, cst, e', d) -> FnHoleR (ht, CS._LRorRec cst, e', d)
          | _ -> f e);
      on_var = identity;
      on_const = identity;
    }
    e

let set_hole_depths e d =
  transform_expr2
    {
      case = (fun e -> match e with FnHoleL _ | FnHoleR _ -> true | _ -> false);
      on_case =
        (fun f e ->
          match e with
          | FnHoleL (ht, var, cst, e', _) -> FnHoleL (ht, var, cst, e', d)
          | FnHoleR (ht, cst, e', _) -> FnHoleR (ht, cst, e', d)
          | _ -> f e);
      on_var = identity;
      on_const = identity;
    }
    e

(**
   Replace expression n time. Returns a list of expressions, with all
   the possible combinations.
*)
let replace_many ?(_in_subscripts = false) ~to_replace:tr ~by:b expr n =
  (* Count how many expressions have to be replaced, and then using a mutable
     counter replace expressions depending on counter. For each possible
     combination, give the indexes that have to be replaced. *)
  let num_occ =
    rec_expr2
      {
        init = 0;
        join = (fun a b -> a + b);
        case = (fun e -> e = tr);
        on_case = (fun _ _ -> 1);
        on_var = (fun _ -> 0);
        on_const = (fun _ -> 0);
      }
      expr
  in
  let repl_indexed il =
    let cntr = ref 0 in
    transform_expr2
      {
        case = (fun e -> e = tr);
        on_var = (fun v -> v);
        on_case =
          (fun _ e ->
            incr cntr;
            if List.mem !cntr il then b else e);
        on_const = (fun c -> c);
      }
      expr
  in
  if num_occ <= 0 then [ expr ]
  else
    let index_to_repl = k_combinations n (1 -- num_occ) in
    List.map repl_indexed index_to_repl

let apply_substutions subs e =
  let case e = match e with FnVar (FnVariable _) -> true | _ -> false in
  let case_handler rfunc e =
    match e with
    | FnVar (FnVariable vi) -> ( try IM.find vi.vid subs with Not_found -> e)
    | _ -> rfunc e
  in
  let const_handler c = c in
  let var_handler v = v in
  transform_expr case case_handler const_handler var_handler e

let replace_expression_in_subscripts ~to_replace:tr ~by:b exp =
  let case _ = false in
  let case_handler _ e = e in
  let const_handler c = c in
  let var_handler v =
    match v with
    | FnArray (v, e) -> FnArray (v, replace_expression ~in_subscripts:true ~to_replace:tr ~by:b e)
    | _ -> v
  in
  transform_expr case case_handler const_handler var_handler exp

let replace_all_subs ~tr:el ~by:oe ~ine:e =
  assert (List.length el = List.length oe);
  List.fold_left2 (fun ne tr b -> replace_expression_in_subscripts ~to_replace:tr ~by:b ne) e el oe

let fn_uses vs expr =
  let join a b = a || b in
  let case _ = false in
  let case_handler _ _ = false in
  let const_handler _ = false in
  let var_handler v = try VarSet.mem (check_option (vi_of v)) vs with Not_found -> false in
  rec_expr join false case case_handler const_handler var_handler expr

(** Operator complexity of a function or an expression *)
let optype_rec =
  {
    join = join_optypes;
    init = NotNum;
    case = (fun e -> match e with FnUnop (_, _) -> true | FnBinop (_, _, _) -> true | _ -> false);
    on_case =
      (fun f e ->
        match e with
        | FnUnop (op, e) -> join_optypes (optype_of_unop op) (f e)
        | FnBinop (op, e1, e2) -> join_optypes (join_optypes (optype_of_binop op) (f e1)) (f e2)
        | _ -> NotNum);
    on_const = (fun _ -> NotNum);
    on_var = (fun _ -> NotNum);
  }

let analyze_optype (e : fnExpr) : operator_type = rec_expr2 optype_rec e

let rec remove_empty_binds : fnExpr -> fnExpr option = function
  | FnLetIn (ve_list, letin) -> (
      match remove_empty_binds letin with
      | Some let_tail -> (
          match ve_list with [] -> Some let_tail | _ -> Some (FnLetIn (ve_list, let_tail)))
      | None -> ( match ve_list with [] -> None | _ -> Some (wrap_state ve_list)))
  | FnRecord (vs, emap) -> if IM.cardinal emap = 0 then None else Some (FnRecord (vs, emap))
  | e -> Some e

let rec remove_empty_lets : fnExpr -> fnExpr = function
  | FnLetIn (b, e) -> (
      let e' = remove_empty_lets e in
      match b with [] -> e' | _ -> FnLetIn (b, e'))
  | e -> e

(** Compose a function by adding new assignments *)
let rec remove_id_binding func =
  let aux_rem_from_list el = List.filter (fun (v, e) -> not (e = FnVar v)) el in
  match func with
  | FnLetIn (el, c) -> FnLetIn (aux_rem_from_list el, remove_id_binding c)
  | _ -> func

let rec compose func1 func2 =
  match func1 with
  | FnLetIn (el, c) -> FnLetIn (el, compose c func2)
  | FnRecord (vs, emap) ->
      (remove_id_binding --> remove_empty_lets) (FnLetIn (unwrap_state vs emap, func2))
  | _ -> func2

let compose_head assignments func =
  match assignments with [] -> func | _ -> FnLetIn (assignments, func)

let rec compose_tail (final : VarSet.t) (assignments : (fnLVar * fnExpr) list) (func : fnExpr) :
    fnExpr =
  match assignments with
  | [] -> func
  | _ -> (
      match func with
      | FnRecord (vs, emap) ->
          let bindings = unwrap_state vs emap in
          let pre, post =
            let rec f (pre, post) l =
              match l with
              | [] -> (pre, post)
              | (v, e) :: tl ->
                  let var = var_of_fnvar v in
                  if VarSet.mem var final then f (pre, post @ [ (v, e) ]) tl
                  else f (pre @ post @ [ (v, e) ], []) tl
            in
            f ([], []) assignments
          in
          remove_id_binding (FnLetIn (bindings, FnLetIn (pre, wrap_state post)))
      | FnLetIn (el, l) -> FnLetIn (el, compose_tail final assignments l)
      | _ -> func)

let complete_with_state (stv : VarSet.t) (el : (fnLVar * fnExpr) list) =
  let emap =
    List.fold_left
      (fun map (v, e) ->
        let vi = check_option (vi_of v) in
        IM.set vi.vid (v, e) map)
      IM.empty el
  in
  let map' =
    VarSet.fold
      (fun vi map -> if IM.mem vi.vid map then map else IM.set vi.vid (mkVar vi, mkVarExpr vi) map)
      stv emap
  in
  let _, velist = Base.List.unzip (IM.bindings map') in
  velist

let rec complete_final_state (vars : VarSet.t) (func : fnExpr) : fnExpr =
  match func with
  | FnRecord (vs, emap) ->
      let to_add = VarSet.diff vars vs in
      FnRecord
        ( VarSet.union vars vs,
          VarSet.fold
            (fun var emap' ->
              if IM.mem var.vid emap' then emap' else IM.set var.vid (mkVarExpr var) emap')
            to_add emap )
  | FnLetIn (el, l) -> FnLetIn (el, complete_final_state vars l)
  | _ -> func

let rec extend_final_state (vars : VarSet.t) (extension : fnExpr IM.t) (func : fnExpr) : fnExpr =
  match func with
  | FnRecord (vs, emap) -> FnRecord (VarSet.union vars vs, IM.add_all emap extension)
  | FnLetIn (el, l) -> FnLetIn (el, extend_final_state vars extension l)
  | _ -> func

let rec used_in_fnexpr (expr : fnExpr) : VarSet.t =
  let join = VarSet.union in
  let init = VarSet.empty in
  let case _ = false in
  let case_h _ _ = VarSet.empty in
  let rec var_handler v =
    match v with
    | FnVariable vi -> VarSet.singleton vi
    | FnArray (v0, e) -> VarSet.union (var_handler v0) (used_in_fnexpr e)
  in
  let const_handler _ = VarSet.empty in
  rec_expr join init case case_h const_handler var_handler expr

let rec used_in_fnlet = function
  | FnLetIn (ve_list, letin) ->
      let bs1, us1 = used_in_fnlet letin in
      let bs2, us2 = used_in_assignments ve_list in
      (VarSet.union bs1 bs2, VarSet.union us1 us2)
  | e -> (VarSet.empty, used_in_fnexpr e)

and used_in_assignments ve_list =
  List.fold_left
    (fun (bind_set, use_set) (v, e) ->
      ( VarSet.union bind_set
          (match vi_of v with Some vi -> VarSet.singleton vi | None -> VarSet.empty),
        VarSet.union use_set (used_in_fnexpr e) ))
    (VarSet.empty, VarSet.empty) ve_list

let has_loop (e : fnExpr) : bool =
  let loopcons _ e = match e with FnRec _ -> true | _ -> false in
  rec_expr2
    {
      join = ( || );
      init = false;
      case = loopcons identity;
      on_case = loopcons;
      on_var = (fun _ -> false);
      on_const = (fun _ -> false);
    }
    e

let indexof (_, g, u) =
  try VarSet.max_elt (VarSet.inter (used_in_fnexpr g) (used_in_fnexpr u))
  with Not_found -> failhere __FILE__ "make_loop_join" "Loop to drill has no index."

let last_expr (vars : VarSet.t) (expr : fnExpr) =
  let rec aux e x =
    match e with
    | FnLetIn (l, e0) ->
        aux e0
          (IM.add_all x
             (IM.of_alist
                (List.filter
                   (fun (vid, _) -> VarSet.has_vid vars vid)
                   (List.map (fun (v, e) -> ((var_of_fnvar v).vid, e)) l))))
    | FnRecord (_, emap) -> IM.add_all x (IM.filter (fun k _ -> VarSet.has_vid vars k) emap)
    | _ -> x
  in
  aux expr IM.empty

let rec unmodified_vars (state : VarSet.t) (expr : fnExpr) =
  match expr with
  | FnLetIn (binds, expr') ->
      let state' =
        VarSet.diff state
          (* Set of modified vars *)
          (List.fold_left
             (fun u (v, e) ->
               match e with FnVar v' when v' = v -> u | _ -> VarSet.add (var_of_fnvar v) u)
             VarSet.empty binds)
      in
      unmodified_vars state' expr'
  | FnRecord (_, emap) ->
      VarSet.filter
        (fun var ->
          try
            match IM.find var.vid emap with
            | FnVar (FnVariable var') -> var'.vid = var.vid
            | _ -> false
          with _ -> true)
        state
  | _ -> state

let split_bindings (expr : fnExpr) =
  let rec aux e (pre, post) =
    match e with
    | FnLetIn (l, e') -> (
        match all_record_accessors l with
        | Some _ -> aux e' (pre @ l, post)
        | None -> aux e' (pre, post @ l))
    | FnRecord (vs, emap) -> (
        let l = unwrap_state vs emap in
        match all_record_accessors l with Some _ -> (pre @ l, post) | None -> (pre, post @ l))
    | _ -> (pre, post)
  in
  aux expr ([], [])

(* The input is a function with one or more loops inside *)
let fuse_loops_for_sketching (func : fnExpr) : fnExpr =
  let rec collect_loops l e =
    match e with
    | FnLetIn (bindings, expr) -> collect_loops (collect_bound bindings l) expr
    | FnRecord (vs, emap) -> collect_bound (unwrap_state vs emap) l
    | _ -> l
  and collect_bound bindings l =
    match bindings with
    | [] -> l
    | (v, e) :: tl -> (
        match e with
        | FnRec _ -> collect_bound tl (l @ [ (v, e) ])
        | _ -> collect_bound tl (collect_loops l e))
  in
  let rec replace_loops ((l1, l) : (fnV * fnLVar * fnExpr) * VarSet.t) (e : fnExpr) : fnExpr =
    match e with
    | FnLetIn (bindings, expr) ->
        FnLetIn (replace_in_bindings (l1, l) bindings, replace_loops (l1, l) expr)
    | FnRecord (_, _) -> e
    | _ -> e
  and replace_in_bindings ((v, v1, l1), rm) bindings =
    match bindings with
    | [] -> []
    | (v', e') :: tl ->
        if VarSet.mem (var_of_fnvar v') rm then replace_in_bindings ((v, v1, l1), rm) tl
        else if v' = v1 then (FnVariable v, l1) :: replace_in_bindings ((v, v1, l1), rm) tl
        else (v', e') :: replace_in_bindings ((v, v1, l1), rm) tl
  in
  (* Remove loop to be fused *)
  (* Update loop fused *)
  let fuse_loop (_, v1, loop1) (_, loop2) =
    match (loop1, loop2) with
    | FnRec ((i1, g1, u1), (vs1, bs1), (s1, body1)), FnRec ((i2, g2, u2), (vs2, bs2), (s2, body2))
      ->
        let index1, index2 = (indexof (i1, g1, u1), indexof (i2, g2, u2)) in
        let i, g, u = (i1, g1, u1) in
        let vs = VarSet.union vs1 vs2 in
        let bs =
          match (bs1, bs2) with
          | FnRecord (_, emap1), FnRecord (_, emap2) -> FnRecord (vs, IM.add_all emap1 emap2)
          | _ -> failwith "Expected start state to be a record."
        in
        let s = mkFnVar "_fs" (record_type vs) in
        let body =
          let _, c2 = split_bindings body2 in
          let l0 = complete_final_state vs (compose_tail vs c2 body1) in
          let l1 = FnLetIn (bind_state ~state_rec:s (VarSet.diff vs vs1), l0) in
          let f1 e = replace_expression ~to_replace:(mkVarExpr s1) ~by:(mkVarExpr s) e in
          let f2 e = replace_expression ~to_replace:(mkVarExpr s2) ~by:(mkVarExpr s) e in
          let f3 e = replace_expression ~to_replace:(mkVarExpr index2) ~by:(mkVarExpr index1) e in
          remove_empty_lets ((f2 --> f1 --> f3) l1)
        in
        let v' = mkFnVar "_res" (record_type vs) in
        (v', v1, FnRec ((i, g, u), (vs, bs), (s, body)))
    | _, _ -> failwith "Expected two loops for fusion."
  in
  let all_loops = collect_loops [] func in
  let final_func =
    if List.length all_loops >= 2 then
      let v1, loop1 = List.hd all_loops in
      let to_remove = List.tl all_loops in
      let v, v1, loop = List.fold_left fuse_loop (var_of_fnvar v1, v1, loop1) to_remove in
      let v_to_rem = VarSet.of_list (List.map (fun (v, _) -> var_of_fnvar v) to_remove) in
      let f' = remove_empty_lets (replace_loops ((v, v1, loop), v_to_rem) func) in
      List.fold_left
        (fun ef (v', _) -> replace_expression ~to_replace:(FnVar v') ~by:(mkVarExpr v) ef)
        f' all_loops
    else func
  in
  final_func

(** ------------------------ 5 - SCHEME <-> FUNC -------------------------- *)

(** Translate basic scheme to the Func expressions
    @param env a mapping from variable ids to varinfos.
*)
let errmsg_unexpected_fnlet unex_let =
  fprintf str_formatter "Expected a translated expression,received for tranlsation @; %a @."
    RAst.pp_expr unex_let;
  flush_str_formatter ()

let errmsg_unexpected_expr ex_type unex_expr =
  fprintf str_formatter "Expected a %s ,received for tranlsation @; %a @." ex_type RAst.pp_expr
    unex_expr;
  flush_str_formatter ()

type join_translation_info = {
  mutable initial_vars : VarSet.t;
  mutable initial_state_vars : VarSet.t;
  mutable used_vars : fnV SH.t;
  mutable used_state_vars : VarSet.t;
  initial_state_right : fnV IH.t;
  initial_state_left : fnV IH.t;
}

let get_binop_of_scm (op : RAst.op) : symb_binop =
  match op with
  | Plus -> Plus
  | Minus -> Minus
  | Mul -> Times
  | Div -> Div
  | Mod -> Mod
  | Eq -> Eq
  | Neq -> Neq
  | Lt -> Lt
  | Leq -> Le
  | Gt -> Gt
  | Geq -> Ge
  | And -> And
  | Or -> Or
  | Min -> Min
  | Max -> Max
  | Not -> failwith "Scm to fn : Not is not a binary operator !"
  | _ -> failwith "Car, cdr, Null and Load are not yet supported"

let get_unop_of_scm (op : RAst.op) : symb_unop =
  match op with Not -> Not | _ -> failwith "Scheme unary operator not supported"

let co = check_option

let join_info =
  {
    initial_vars = VarSet.empty;
    initial_state_vars = VarSet.empty;
    used_vars = SH.create 10;
    used_state_vars = VarSet.empty;
    initial_state_right = IH.create 10;
    initial_state_left = IH.create 10;
  }

let init_scm_translate all_vs state_vs =
  join_info.initial_vars <- all_vs;
  join_info.initial_state_vars <- state_vs

(** Find varinfo assiociated to a name, possibly prefixed
    by the class instance representing the right-state input
    in the join function.
    Create adequate variables when not existing, and memorizes
    which variable are in use.
*)
let scm_find_varname s =
  let pure_varname, _is_class_member, _is_right_state_mem = is_right_state_varname s in
  try
    let varinfo : fnV = find_var_name pure_varname in
    { varinfo with vname = s }
  with Not_found ->
    printf "[WARNING] Did not find variable %s when parsing solution of solver.@." pure_varname;
    printf "          Continuing anyway ...@.";
    mkFnVar (get_new_name ~base:s ()) Bottom

let hole_var_name = "??_hole"

let hole_var = mkFnVar hole_var_name Bottom

let from_accessor a s =
  if is_struct_accessor a then
    let member_name = List.nth (Str.split (Str.regexp "-") a) 1 in
    let state =
      try find_var_name s
      with Not_found -> failhere __FILE__ "from_accessor" ("State not found : " ^ s)
    in
    FnRecordMember (mkVarExpr state, member_name)
  else
    let msg =
      fprintf str_formatter "Expected a struct accessor received %s" a;
      flush_str_formatter ()
    in
    failhere __FILE__ "from_accessor" msg

let remove_hole_vars (expr : fnExpr) : fnExpr =
  let rec aux_rem_h t e =
    match e with
    | FnVar (FnVariable v) when v = hole_var -> (
        match t with Num -> FnConst (CInt 0) | _ -> FnConst (CBool true))
    | FnBinop (op, e1, e2) ->
        let tdown = type_of_binop_args op in
        FnBinop (op, aux_rem_h tdown e1, aux_rem_h tdown e2)
    | FnUnop (op, e0) ->
        let tdown = type_of_unop_args op in
        FnUnop (op, aux_rem_h tdown e0)
    | FnCond (c, e1, e2) -> FnCond (aux_rem_h Boolean c, aux_rem_h t e1, aux_rem_h t e2)
    | FnApp (t, vo, el) -> FnApp (t, vo, List.map (fun e -> aux_rem_h Unit e) el)
    | FnRecord (vs, emap) -> FnRecord (vs, IM.map (fun e -> aux_rem_h Unit e) emap)
    | FnLetIn (ve_list, letin) ->
        FnLetIn (List.map (fun (v, e) -> (v, aux_rem_h Unit e)) ve_list, aux_rem_h Unit letin)
    | e -> e
  in
  aux_rem_h Unit expr

let rec scm_to_fn (scm : RAst.expr) : fnExpr =
  let unwrap_fun_e e = match e with RAst.Fun_e (_, e') -> e' | e -> e in
  let get_fun_state e =
    match e with
    | RAst.Fun_e (il, _) -> find_var_name (List.nth il 0)
    | _ -> failwith "get_fun_state only on fun_e"
  in
  let rec translate (scm : RAst.expr) : fnExpr =
    try
      match scm with
      | Int_e i -> FnConst (CInt i)
      | Float_e f -> FnConst (CReal f)
      | Str_e s -> FnConst (CString s)
      | Bool_e b -> FnConst (CBool b)
      | Id_e id -> (
          match id with
          | "??" -> FnVar (FnVariable hole_var)
          | _ ->
              let vi = scm_find_varname id in
              FnVar (FnVariable vi))
      | Nil_e -> FnConst CNil
      | Binop_e (op, e1, e2) ->
          let e1' = translate e1 in
          let e2' = translate e2 in
          FnBinop (get_binop_of_scm op, e1', e2')
      | Unop_e (op, e) ->
          let e' = translate e in
          FnUnop (get_unop_of_scm op, e')
      | Cons_e (_, _) -> failwith "Cons not supported"
      | Let_e (bindings, e2) | Letrec_e (bindings, e2) ->
          let fn_bindings =
            List.map
              (fun (ids, e) ->
                let exp = translate e in
                let vi = scm_find_varname ids in
                (FnVariable vi, exp))
              bindings
          in
          let fn_let = translate e2 in
          FnLetIn (fn_bindings, fn_let)
      | If_e (c, e1, e2) ->
          let cond = translate c in
          let le1 = translate e1 in
          let le2 = translate e2 in
          FnCond (cond, le1, le2)
      | Apply_e (e, arglist) -> (
          match e with Id_e s -> translate_id_func s e arglist | _ -> translate e)
      | Fun_e (il, _) ->
          let es =
            pp_space_sep_list (fun fmt s -> fprintf fmt "%s" s) str_formatter il;
            flush_str_formatter ()
          in
          failhere __FILE__ "scm_to_fn" ("Fun_e : Not supported, ids: " ^ es)
      | Def_e _ -> failhere __FILE__ "scm_to_fn" "Def_e : definition not supported."
      | Defrec_e _ -> failhere __FILE__ "scm_to_fn" "Defrec_e : definitions not supported."
      | Delayed_e _ | Forced_e _ ->
          failhere __FILE__ "scm_to_fn" "Delayed_e or Forced_e not suppported."
    with Not_found ->
      eprintf "expression : %a" RAst.pp_expr scm;
      failwith "Variable name not found in current environment."
  and translate_id_func s e arglist =
    match s with
    | "list-ref" -> FnVar (to_array_var arglist)
    | "LoopFunc" -> translate_loop arglist
    | "make-list" -> (
        let ln =
          match List.hd arglist with
          | Int_e i -> i
          | _ -> failhere __FILE__ __LOC__ "Parsed make-list without length integer."
        in
        let v = translate (List.nth arglist 1) in
        match v with
        | FnConst c -> FnConst (CArrayInit (ln, c))
        | _ -> FnVector (ListTools.init ln (fun _ -> v)))
    | a when is_struct_accessor s -> (
        match arglist with
        | [ Id_e s ] -> from_accessor a s
        | _ -> failhere __FILE__ __LOC__ "Bad accessor")
    | _ when is_name_of_struct s -> rosette_state_struct_to_fnlet s arglist
    | "identity" -> translate (List.nth arglist 0)
    | "list-set" ->
        let i = translate (List.nth arglist 1) in
        let e = translate (List.nth arglist 2) in
        let a = translate (List.nth arglist 0) in
        FnArraySet (a, i, e)
    | _ -> to_fun_app e arglist
  and translate_loop arglist =
    if List.length arglist = 5 then
      let init = translate (unwrap_fun_e (List.nth arglist 0)) in
      let guard = translate (unwrap_fun_e (List.nth arglist 1)) in
      let update = translate (unwrap_fun_e (List.nth arglist 2)) in
      let __s = get_fun_state (List.nth arglist 4) in
      let stv =
        match __s.vtype with
        | Record (name, _) -> snd (get_struct name)
        | _ -> failhere __FILE__ "translate scm" "Expected a record type."
      in
      let stv_init =
        match List.nth arglist 3 with
        | RAst.Apply_e (_, inits) -> (
            try
              FnRecord
                ( stv,
                  List.fold_left2
                    (fun emap v ei -> IM.set v.vid (translate ei) emap)
                    IM.empty (VarSet.elements stv) inits )
            with Invalid_argument _ ->
              failhere __FILE__ "translate_loop" "Mismatch in state vars/ args.")
        | _ -> failhere __FILE__ "translate scm" "Expected a record expression."
      in
      FnRec
        ( (init, guard, update),
          (stv, stv_init),
          (__s, translate (unwrap_fun_e (List.nth arglist 4))) )
    else failhere __FILE__ "scm_to_fn" "LoopFunc macro with more than 5 args."
  in
  translate scm

(** Structure translation is parameterized by the current information
    loaded in the join_info. The order had been created using the order in
    the set of state variables so we use the same order to re-build the
    expressions.
    Additionally we remove identity bindings.
*)
and rosette_state_struct_to_fnlet sname scm_expr_list =
  let stv_vars_list = VarSet.elements join_info.initial_state_vars in
  let fn_expr_list = to_expression_list scm_expr_list in
  try
    let id_expr_binds =
      Base.List.zip_exn (List.map (fun vi -> vi.vid) stv_vars_list) fn_expr_list
    in
    FnRecord (join_info.initial_state_vars, IM.of_alist id_expr_binds)
  with Invalid_argument _ -> (
    (* Might be an inner state struct. *)
    try
      let _, vs = get_struct sname in
      FnRecord (vs, IM.of_alist (Base.List.zip_exn (VarSet.vids_of_vs vs) fn_expr_list))
    with
    | Not_found ->
        eprintf
          "FAILURE :@\n\
           Failed to translate state in list of bindings, got %i state variables and state was %i \
           long.@\n\
           ---> Did you initialize the join_info before using scm_to_fn ?"
          (VarSet.cardinal join_info.initial_state_vars)
          (List.length fn_expr_list);
        failwith "Failure in rosette_state_struct_to_fnlet."
    | _ -> failhere __FILE__ "rosette_state_struct_to_fnlet" "Failed to guess state.")

and to_expression_list scm_expr_list = List.map scm_to_fn scm_expr_list

and to_array_var scm_expr_list =
  let array_varinfo =
    match List.nth scm_expr_list 0 with
    | RAst.Id_e varname -> scm_find_varname varname
    | e -> raise (Failure (errmsg_unexpected_expr "identifier" e))
  in
  let offset_list = to_expression_list (List.tl scm_expr_list) in
  mkVar ~offsets:offset_list array_varinfo

and to_fun_app ?(_typ = Bottom) fun_expr scm_expr_list =
  try
    let args = to_expression_list scm_expr_list in
    match fun_expr with
    | Id_e fun_name -> (
        match (symb_binop_of_fname fun_name, symb_unop_of_fname fun_name) with
        | Some binop, _ -> FnBinop (binop, List.nth args 0, List.nth args 1)
        | _, Some unop -> FnUnop (unop, List.nth args 0)
        | None, None ->
            let fun_vi = scm_find_varname fun_name in
            FnApp (Bottom, Some fun_vi, args))
    | _ -> raise (Failure (errmsg_unexpected_expr "identifier" fun_expr))
  with _ -> failhere __FILE__ "to_fun_app" "Error in function translation."

let scm_to_const e =
  match scm_to_fn e with
  | FnConst c -> c
  | _ -> failhere __FILE__ "scm_to_const" "Expected a const."

let force_flat vs fnlet =
  let rec force_aux fnlet subs =
    match fnlet with
    | FnLetIn (ve_list, letin) ->
        let subs_copy = subs in
        force_aux letin
          (List.fold_left
             (fun new_subs (v, e) ->
               try
                 let vi = co (vi_of v) in
                 IM.set vi.vid (apply_substutions subs_copy e) new_subs
               with Failure _ -> new_subs)
             subs ve_list)
    | FnRecord (vs, emap) ->
        let final_subs =
          IM.fold
            (fun i e new_subs ->
              try IM.set i (apply_substutions subs e) new_subs with Failure _ -> new_subs)
            emap subs
        in
        FnRecord
          ( vs,
            IM.fold
              (fun vid e emap -> IM.set (VarSet.find_by_id vs vid).vid e emap)
              final_subs IM.empty )
    | _ -> failhere __FILE__ "force_flat" "Not a proper function."
  in
  let start_sub =
    VarSet.fold (fun vi subs -> IM.set vi.vid (FnVar (FnVariable vi)) subs) vs IM.empty
  in
  force_aux fnlet start_sub

(** ------------------------ 6 - EXPRESSION SETS -----------------------------*)

module ES = Set.Make (struct
  let compare = compare

  type t = fnExpr
end)

let es_transform f es = ES.of_list (List.map f (ES.elements es))

type context = {
  state_vars : VarSet.t;
  index_vars : VarSet.t;
  used_vars : VarSet.t;
  all_vars : VarSet.t;
  costly_exprs : ES.t;
}
(** Context for expression analysis *)

let mk_ctx vs stv =
  {
    state_vars = stv;
    index_vars = VarSet.empty;
    used_vars = VarSet.diff stv vs;
    all_vars = vs;
    costly_exprs = ES.empty;
  }

let ctx_inter (ctx : context) (vs : VarSet.t) : context =
  { ctx with state_vars = VarSet.inter vs ctx.state_vars; index_vars = ctx.index_vars }

let ctx_update_vsets ctx vs =
  let new_allvs = VarSet.union ctx.all_vars vs in
  let new_usedvs = VarSet.union ctx.used_vars vs in
  let new_stvs = VarSet.union ctx.state_vars vs in
  { ctx with state_vars = new_stvs; used_vars = new_usedvs; all_vars = new_allvs }

let ctx_add_cexp ctx cexp = { ctx with costly_exprs = cexp }

(** ------------------- 7 - INDEX VARIABLES MANAGEMENT ----------------------*)

(** Create and manage variables for index boundaries *)

(* Extract boundary variables "n" from func information *)
let get_loop_bound_var (se : fnExpr) : fnExpr option =
  match se with FnBinop (Lt, _, en) -> Some en | FnBinop (Le, _, ene) -> Some ene | _ -> None

(** Really not here to last ... must find a better way to differentiate
    the expressions. *)
let is_prefix_or_suffix _vi expr = match expr with FnVar (FnArray (_, _)) -> true | _ -> false

(* ------------------------ 8 - STRUCT UTILS ----------------------------*)

type sigu = VarSet.t * (fnExpr * fnExpr * fnExpr)

type func_dec = {
  (* The variable that has the name and the type of the function. *)
  fvar : fnV;
  (* The lsit of variables that represent the arguments of the function
     by name and type.
  *)
  fformals : fnV list;
  (* The local variables of the function. *)
  flocals : fnV list;
}

type prob_rep = {
  (* The id of the problem, unique and should not be modified. *)
  id : int;
  (* host_function describes the host function of the loop. See
     the definition of func_dec type for more information.
  *)
  host_function : func_dec;
  (* The name of the loop, generated using the truncated name of the
        host function and the line number. For more information on how the
     name is generated in the main flow of the tool, see Canalyst.ml.
        It uses Config.inner_loop_func_name (see the Conf library)
  *)
  loop_name : string;
  (* The context of the loop, storing information about the index
     variables of the loop. See the definition of the context type
     for more information.
  *)
  scontext : context;
  (* min_input_size is the minimal size of the input for the loop to
     be well defined. For example, if a loop uses the expression a[i-1] and
     the index of the loop i starts at 0, then the input of the loop (the
     array a) needs to be at least 1.
     Still experimental.
  *)
  min_input_size : int;
  (* Experimental. Ignore for now... *)
  uses_global_bound : bool;
  (* The loop body. It is the expression of a function representing the
     body of the loop. To understand how to use this loop body inside a
     recursive function, have a look at Sketch.pp_loop_body that prints the
     body with some context information, inside a recursive function.
  *)
  main_loop_body : fnExpr;
  (* Store different loop body versions, the inner loop / inner join
     solution will need to be inlined / abstracted at different points of the
     analysis.
  *)
  loop_body_versions : fnExpr SH.t;
  (* The sketch of the join. Not used if it is an inner loop.
     To understand how it is used, see Sketch.pp_join and Sketch.pp_join_body
  *)
  join_sketch : fnExpr;
  (* The sketch of the memoryless join. Useless if this is an outer loop.
     To understand how it is used, see Sketch.pp_join and Sketch.pp_join_body
  *)
  memless_sketch : fnExpr;
  (* The solution of the join sketch. Does not necessarily correspond exactly
     to filling the holes of the join sketch, because some optimizations /
        simplifcations might have been performed here.
  *)
  join_solution : fnExpr;
  (* Similar to above, but for the memoryless join. *)
  memless_solution : fnExpr;
  (* Store for the init values that have been found by solving the sketch.
     This map uses variable names used in the sketch to bind non-translated
     expressions returned by the solver to the variables of the problem.
     Should represent:
     STATE VARIABLE ID --> INITIAL VALUE IN THE JOIN SKETCH SOLUTION
  *)
  init_values : RAst.expr IM.t;
  (* SImilar to the above, but identity values. Only used in the memoryless
     join for now, to find the initial state s0.
  *)
  identity_values : constants IM.t;
  (* The loop's initial value, index guard and index update. See
     Sketch.pp_loop for more information.
  *)
  func_igu : sigu;
  (* Maps variable ids to the value of the state variable reaching the
     loop.
  *)
  reaching_consts : fnExpr IM.t;
  (* The list of inner loops, translated to functional form.*)
  mutable inner_functions : prob_rep list;
}

let mkFuncDec (fun_var, formals, locals) : func_dec =
  {
    fvar = var_of_vi fun_var;
    fformals = List.map var_of_vi formals;
    flocals = List.map var_of_vi locals;
  }

let get_index_init problem =
  let _, (i, _, _) = problem.func_igu in
  i

let get_index_update problem =
  let _, (_, _, u) = problem.func_igu in
  u

let get_index_varset problem =
  let idx, (_, _, _) = problem.func_igu in
  idx

let get_index_guard problem =
  let _, (_, g, _) = problem.func_igu in
  g

let get_init_value problem vi =
  try IM.find vi.vid problem.reaching_consts
  with Not_found -> scm_to_fn (IM.find vi.vid problem.init_values)

let get_loop_bound problem = get_loop_bound_var (get_index_guard problem)

let get_bounds problem =
  let bvar = VarSet.max_elt (get_index_varset problem) in
  try (find_var_name (bvar.vname ^ "_start"), find_var_name (bvar.vname ^ "_end"))
  with Not_found ->
    (mkFnVar (bvar.vname ^ "_start") bvar.vtype, mkFnVar (bvar.vname ^ "_end") bvar.vtype)

let set_pb_hole_depths (pb : prob_rep) (d : int) =
  {
    pb with
    memless_sketch = set_hole_depths pb.memless_sketch d;
    join_sketch = set_hole_depths pb.join_sketch d;
  }

(* ----------------------- 9 - CONVERSION TO CIL  ----------------------------*)

(** Includes passes to transform the code into an appropriate form *)

let rec pass_remove_special_ops e =
  (transform_expr
     (fun e -> match e with FnBinop _ -> true | FnApp _ -> true | _ -> false)
     (fun rfun e ->
       match e with
       | FnBinop (op, e1, e2) -> (
           let e1' = rfun e1 in
           let e2' = rfun e2 in
           match op with
           | Max -> FnCond (FnBinop (Gt, e1', e2'), e1', e2')
           | Min -> FnCond (FnBinop (Lt, e1', e2'), e1', e2')
           | Nand -> FnUnop (Not, FnBinop (And, e1', e2'))
           | Neq -> FnUnop (Not, FnBinop (Eq, e1, e2))
           | _ -> FnBinop (op, e1', e2'))
       | FnApp (st, vo, args) ->
           let args' = List.map rfun args in
           if List.length args' >= 1 then
             (* Might be a binary operator ... *)
             let e1 = List.nth args' 0 in
             match vo with
             | Some var -> (
                 match String.lowercase_ascii var.vname with
                 | "max" ->
                     let e2 = List.nth args' 1 in
                     FnCond (FnBinop (Gt, e1, e2), e1, e2)
                 | "min" ->
                     let e2 = List.nth args' 1 in
                     FnCond (FnBinop (Lt, e1, e2), e1, e2)
                 | "add1" -> FnBinop (Plus, e1, FnConst (CInt 1))
                 | "sub1" -> FnBinop (Minus, e1, FnConst (CInt 1))
                 | _ -> FnApp (st, vo, args'))
             | None -> FnApp (st, vo, args')
           else FnApp (st, vo, args')
       | FnLetIn (ve_list, letin) ->
           FnLetIn
             ( List.map (fun (v, e) -> (v, pass_remove_special_ops e)) ve_list,
               pass_remove_special_ops letin )
       | FnRecord (vs, emap) -> FnRecord (vs, IM.map (fun e -> pass_remove_special_ops e) emap)
       | _ -> failwith "Bad rec case.")
     identity identity)
    e

let rec pass_sequentialize fnlet =
  let reorganize ve_list let_queue =
    (* A variable should be only bound once in a binding group, therefore
        we can identify a binding only by the variables it binds to.
        We supports only scalar types ! n *)
    let modified_vars, vid_to_expr, _depends_graph_unpure =
      List.fold_left
        (fun (modified_set, expr_map, dep_graph) (v, e) ->
          match e with
          | FnVar v' when v = v' -> (modified_set, expr_map, dep_graph) (* Identity binding *)
          | _ ->
              let vi =
                try check_option (vi_of v)
                with Failure _ -> failwith "Non-scalar type unsupported"
              in
              let expr_depends = used_in_fnexpr e in
              ( VarSet.add vi modified_set,
                IM.set vi.vid e expr_map,
                IM.set vi.vid expr_depends dep_graph ))
        (VarSet.empty, IM.empty, IM.empty)
        ve_list
    in
    (* let depends_graph = IM.map (fun deps -> VarSet.inter deps modified_vars) *)
    (*     depends_graph_unpure *)
    (* in *)
    (* We need to implement here the algorithm described in :
        http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf *)
    let statement_order = VarSet.vids_of_vs modified_vars in
    List.fold_left
      (fun let_bindings vid ->
        FnLetIn
          ( [ (FnVariable (VarSet.find_by_id modified_vars vid), IM.find vid vid_to_expr) ],
            let_bindings ))
      let_queue statement_order
    (* Analyze dependencies to produce bindings ordered such that
        the sequence of bindings yields to the same state as the functional
        version where all expressions are evaluated in one step. *)
  in

  let sequentialize_parallel_moves = function
    | FnLetIn (ve_list, letin) -> reorganize ve_list (pass_sequentialize letin)
    | FnRecord (vs, emap) -> reorganize (unwrap_state vs emap) (FnRecord (vs, identity_map vs))
    | e -> e
  in
  match remove_empty_binds (sequentialize_parallel_moves fnlet) with
  | Some fnlet -> fnlet
  | None -> FnRecord (VarSet.empty, IM.empty)

let fn_for_c fnlet = pass_sequentialize (pass_remove_special_ops fnlet)

(** Let bindings to imperative code. *)
let sort_nb_used_vars (v1, e1) (v2, e2) =
  let used1 = used_in_fnexpr e1 in
  let used2 = used_in_fnexpr e2 in
  let vi1 = check_option (vi_of v1) in
  let vi2 = check_option (vi_of v2) in
  match (VarSet.mem vi1 used2, VarSet.mem vi2 used1) with
  | false, false -> if VarSet.cardinal used1 > VarSet.cardinal used2 then 1 else -1
  | true, false -> 1
  | false, true -> -1
  (* Case with a conflict ! Needs a temp variable. *)
  | true, true -> 1

let used_struct_types (body : fnExpr) : fn_type list =
  let rec extract_of_var v =
    match v with
    | FnVariable v -> ( match v.vtype with Record _ -> [ v.vtype ] | _ -> [])
    | FnArray (a, _) -> extract_of_var a
  in
  let rectypes =
    rec_expr2
      {
        case = (fun e -> match e with FnRecord _ -> true | _ -> false);
        on_case = (fun _ e -> match e with FnRecord (vs, _) -> [ record_type vs ] | _ -> []);
        on_var = extract_of_var;
        on_const = (fun _ -> []);
        init = [];
        join = ( @ );
      }
      body
  in
  ListTools.remove_duplicates rectypes
