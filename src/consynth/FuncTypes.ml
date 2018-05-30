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
open Loops
open RAst
open Sets
open Synthlib
open Synthlib2ast

(**
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
let rosette_prefix_struct = Conf.get_conf_string "rosette_struct_name"
let debug = ref false


(* ---------------------------- 1 - EXPRESSIONS ----------------------------- *)



type hole_type = fn_type * operator_type

(* Type for variables *)
and fnLVar =
  | FnVariable of fnV
  (** Access to an array cell *)
  | FnArray of fnLVar * fnExpr


(* Type for expressions *)
and fnExpr =
  | FnLetExpr of (fnLVar * fnExpr) list
  | FnLetIn of (fnLVar * fnExpr) list * fnExpr
  | FnVar of fnLVar
  | FnConst of constants
  | FnFun of fnExpr
  | FnRec of  (fnExpr * fnExpr * fnExpr) * (VarSet.t * fnExpr) * (fnV * fnExpr)
  | FnCond of fnExpr * fnExpr * fnExpr
  | FnBinop of symb_binop * fnExpr * fnExpr
  | FnUnop of symb_unop * fnExpr
  | FnApp of fn_type * (fnV option) * (fnExpr list)
  | FnHoleL of hole_type * fnLVar * CS.t * fnExpr
  | FnHoleR of hole_type * CS.t * fnExpr
  | FnChoice of fnExpr list
  | FnVector of fnExpr list
  | FnArraySet of fnExpr * fnExpr * fnExpr
  | FnRecord of fn_type * (fnExpr list)
  | FnRecordMember of fnExpr * string
  (** Simple translation of Cil exp needed to nest
      sub-expressions with state variables *)
  | FnSizeof of fn_type
  | FnSizeofE of fnExpr
  | FnSizeofStr of string
  | FnAlignof of fn_type
  | FnAlignofE of fnExpr
  | FnCastE of fn_type * fnExpr
  | FnAddrof of fnExpr
  | FnAddrofLabel of Cil.stmt ref
  | FnStartOf of fnExpr

and fnDefinition = fnV * fnV list * fnExpr

(* Get the varinfo of a variable. *)
let rec vi_of fnlv =
  match fnlv with
  | FnVariable vi' -> Some vi'
  | FnArray (fnlv', _) -> vi_of fnlv'

(* -------------------- 2 - TYPING FUNCTIONS -------------------- *)


let type_of_unop (t : fn_type) : symb_unop -> fn_type option =
  let type_of_unsafe_unop t =
    function
    | _ -> Real
  in
  function
  | Not -> if t = Boolean then Some Boolean else None

  | Neg  | Abs | Add1 | Sub1->
    if is_subtype t Real then Some t else None

  | Floor | Ceiling | Round | Truncate ->
    if is_subtype t Real then Some Integer else None

  | Sgn ->
    if is_subtype t Real then Some Boolean else None

  | UnsafeUnop op ->
    Some (type_of_unsafe_unop t op)


let type_of_binop t1 t2 : symb_binop -> fn_type option =
  let join_t = join_types t1 t2 in
  let type_of_unsafe_binop t1 t2 =
    function
    | _ -> Some Real
  in
  function
  | And | Nand | Xor | Or | Implies | Nor ->
    if is_subtype join_t Boolean then Some Boolean else None

  | Le | Ge | Gt | Lt | Neq ->
    if is_subtype join_t Real then Some Boolean else None

  | Eq  -> Some Boolean

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
  | CArrayInit (n, c) -> type_of_const c
  | CReal _ -> Real
  | CInt _ | CInt64 _ -> Integer
  | CBox b -> Box (type_of_cilconst b)
  | CUnop (op, c) -> type_of (FnUnop (op, FnConst c))
  | CBinop (op, c, c') -> type_of (FnBinop (op, FnConst c, FnConst c'))
  | Pi | SqrtPi | Sqrt2 | E | Ln2 | Ln10 -> Real
  | CUnsafeBinop (op, c, c') -> join_types (type_of_const c) (type_of_const c')
  | CUnsafeUnop (op, c) -> (type_of_const c)
  | Infnty | NInfnty -> Num

and type_of_var v =
  match v with
  | FnVariable vi -> vi.vtype
  | FnArray (v, e) ->
    (** We only consider integer indexes for now *)
    (** Return the type of the array cells *)
    begin
      match type_of_var v with
      | Vector (tv, _) -> tv
      | t -> failwith
               (Format.fprintf Format.str_formatter
                  "Unexpected type %a for variable in array access."
                  pp_typ t ; Format.flush_str_formatter ())
    end


and type_of expr =
  match expr with
  | FnVar v -> type_of_var v
  | FnRecord (t, el) ->
    begin
      match t with
      | Record st ->
        if List.length st = List.length el then
          Record(List.map2 (fun (s,t) e -> (s, type_of e)) st  el)
        else
          failwith "Record with wrong number of arguments."
      | _ -> failwith "Record has no record type."
    end
  | FnConst c -> type_of_const c
  | FnAddrofLabel _ | FnStartOf _
  | FnSizeof _ | FnSizeofE _ | FnSizeofStr _
  | FnAlignof _ | FnAlignofE _  | FnAddrof _ -> Integer
  | FnCastE (t, e) -> t
  | FnUnop (unop, e) ->
    (match type_of_unop (type_of e) unop with
     | Some x -> x | None -> failwith "Could not find type of expressions.")

  | FnBinop (binop, e1, e2) ->
    (match type_of_binop (type_of e1) (type_of e2) binop with
     | Some x -> x | None -> failwith "Could not find type of expressions.")

  | FnCond (c, e1, e2) -> join_types (type_of e1) (type_of e2)

  | FnApp (t, _, _) -> t
  | FnHoleL (ht, _,  _, _) | FnHoleR (ht, _, _) ->
    (match ht with (t, ot) -> t)

  | FnFun e -> Function(type_of e, type_of e)
  | FnVector a -> Vector(type_of (List.nth a 0), Some (List.length a))
  | FnRecordMember(e, s) ->
    begin
      match type_of e with
      | Record slt ->
        (try
          let _, t0 =
            List.hd (List.filter (fun (s',t) -> s = s') slt) in
          t0
        with _ -> failontype "Record member not found in record type.")
      | _ -> failontype "Should be a record type inside a record mmeber access."
    end
  | FnLetIn(_, e) -> type_of e
  | FnLetExpr(el) ->
    Record
      (List.map (fun (v,e) ->
           match vi_of v with
           | Some var -> (var.vname, type_of e)
           | None -> failontype "Cannot create type of final let-binding.") el)
  | FnChoice _ -> Bottom
  | FnArraySet (a, _, _) -> type_of a
  | FnRec(_, _, (s, _)) -> s.vtype


let filter_vs_by_type t =
  VarSet.filter
    (fun vi ->
       vi.vtype = t)

let filter_cs_by_type t =
  CS.filter
    (fun jc ->
       match jc.cvi.vtype with
       | Vector (st, _) -> st = t
       | st -> st = t)

let rec input_type_or_type =
  function
  | Function (it, rt) -> input_type_or_type it
  | t -> t


(** ----------------------- 3 - BASIC HELPER FUNCTIONS -----------------------*)

(* Given a cil operator, return an unary symb operator and a type *)
let symb_unop_of_cil : Cil.unop -> symb_unop * fn_type =
  function
  | Cil.LNot -> Not, Bottom
  | Cil.BNot -> Not, Boolean
  | Cil.Neg -> Neg, Num

(* Given a cil operator, return a binary symb operator and a type *)
let symb_binop_of_cil : Cil.binop -> symb_binop * fn_type =
  function
  | Cil.IndexPI -> Plus, Num
  | Cil.PlusA | Cil.PlusPI -> Plus, Num
  | Cil.MinusA | Cil.MinusPI | Cil.MinusPP-> Minus, Num
  | Cil.Mult -> Times, Num
  | Cil.Div -> Div, Num
  | Cil.Mod -> Mod, Integer
  | Cil.BXor -> Xor, Bitvector 0
  | Cil.BAnd -> And, Bitvector 0
  | Cil.LAnd -> And, Boolean
  | Cil.BOr -> Or, Bitvector 0
  | Cil.LOr -> Or, Boolean
  | Cil.Lt -> Lt, Num | Cil.Le -> Le, Num | Cil.Gt -> Gt, Num
  | Cil.Ge -> Ge, Num
  | Cil.Eq -> Eq, Num | Cil.Ne -> Neq, Num
  | Cil.Shiftlt -> ShiftL, Bitvector 0 | Cil.Shiftrt -> ShiftR, Bitvector 0


(* Return the type associated to a binary operator. *)
let optype_of_binop =
  function
  | Expt | Times | Div -> NonLinear
  | Max | Min -> Basic
  | Plus | Minus -> Arith
  | _ -> NotNum

(* Return the type associated to a unary operator. *)
let optype_of_unop =
  function
  | Truncate | Round | UnsafeUnop _
  | Abs | Floor | Ceiling -> NonLinear
  | Add1 | Sub1 | Neg -> Arith
  | Sgn | Not -> NotNum

(* Join two operator types. Numeral operator types can be ordered,
   Basic < Arith < NonLinear
*)
let join_optypes opt1 opt2 =
  match opt1, opt2 with
  | NonLinear, _ | _, NonLinear -> NonLinear
  | Basic, _ | _, Basic -> Basic
  | Arith, _ | _, Arith -> Arith
  | _, _ -> NotNum        (* Join *)

(* Returns true if the symb operator is a function we have to define in C *)
let is_op_c_fun (op : symb_binop) : bool =
  match op with
  | Max | Min -> true
  | _ -> false

(** The identity function in the functional representation of the func. *)
let identity_fn =
  FnLetExpr ([])

let identity_state vs =
  List.map (fun v -> (FnVariable v, FnVar(FnVariable v))) (VarSet.elements vs)

(** Translate C Standard Library function names in
    functions supported by Rosette
*)
let symb_unop_of_fname =
  function
  | "floor" | "floorf" | "floorl" -> Some Floor
  | "abs"
  | "fabs" | "fabsf" | "fabsl"
  | "labs" | "llabs" | "imaxabs" -> Some Abs
  | "ceil" -> Some Ceiling
  (** C++11 *)
  | "trunc" | "truncf" | "truncl"  -> Some Truncate
  | "lround" | "lroundf" | "lroundl"
  | "round" | "roundf" | "roundl"
  | "nearbyint" | "nearbyintf" | "nearbyintl"
  | "llround" | "llroundf" | "llroundl"
  | "rint" | "rintf" | "rintl" -> Some Round
  | _ -> None

let symb_binop_of_fname : string -> symb_binop option =
  function
  | "modf" | "modff" | "modfl" -> Some Mod
  | "fmod" | "fmodl" | "fmodf" -> Some Mod
  | "remainder" | "remainderf" | "remainderl"
  | "drem" | "dremf" | "dreml" -> Some Rem
  | "max" | "fmax" | "fmaxf" | "fmaxl" -> Some Max
  | "min" | "fmin" | "fminf" | "fminl" -> Some Min
  (**
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
let unsafe_unops_of_fname =
  function
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

let unsafe_binops_of_fname =
  function
  | _ -> None


let is_comparison_op : symb_binop -> bool=
  function
  | Eq | Gt | Lt | Le | Ge -> true
  | _ -> false
(**
    Mathematical constants defined in GNU-GCC math.h.
   + other custom constants defined in the decl_header.c

    TODO : integrate log/ln/pow function, not in
    rosette/safe AFAIK.
*)

(* Some predefined constatns in C can be translated to expressions
   in the func functional represenation.out_newline.
*)

let c_constant  ccst =
  match ccst with
  | s when Conf.is_builtin_var s ->

    (match Conf.get_builtin s with
     | Conf.Max_Int -> Some Infnty
     | Conf.Min_Int -> Some NInfnty
     | Conf.True -> Some (CBool true)
     | Conf.False -> Some (CBool false))

  | "M_E" -> Some E
  | "M_LN2" -> Some Ln2
  | "M_LN10" -> Some Ln10
  | "M_PI" -> Some Pi
  | "M_PI_2" -> Some (CBinop (Div, Pi, (CInt 2)))
  | "M_PI_4" -> Some (CBinop (Div, Pi, (CInt 2)))
  | "M_1_PI" -> Some (CBinop (Div, (CReal 1.0), Pi))
  | "M_2_PI" -> Some (CBinop (Div, (CReal 2.0), Pi))
  | _ ->
    if !use_unsafe_operations then
      begin
        match ccst with
        | "M_SQRT2" -> Some Sqrt2
        | "M_SQRT1_2" ->
          Some (CBinop (Div, (CReal 1.0), Sqrt2))
        | "M_2_SQRTPI" ->
          Some (CBinop (Div, (CReal 2.0), SqrtPi))
        | "M_LOG10E" ->
          Some (CBinop (Div, (CReal 1.0), Ln10))
        | "M_LOG2E" ->
          Some (CBinop (Div, (CReal 1.0), Ln2))
        | _ -> None
      end
    else
      None

(* Returns true if a constant is negative. *)
let is_negative cst =
  match cst with
  | CInt i -> i< 0
  | CInt64 i -> i < 0L
  | CReal f -> f < 0.0
  | _ -> false



(**
    A function name not appearing in the cases above
    will be treated as an "uninterpreted function" by
    default.
*)

let uninterpeted fname =
  let not_in_safe =
    match symb_unop_of_fname fname with
    | Some _ -> false
    | None ->
      begin
        match symb_binop_of_fname fname with
        | Some _ -> false
        | None ->
          begin
            match c_constant fname with
            | Some _ -> false
            | None -> true
          end
      end
  in
  let not_in_unsafe =
    if !use_unsafe_operations
    then
      begin
        match unsafe_unops_of_fname fname with
        | Some _ -> false
        | None -> true
      end
    else true
  in
  not_in_safe && not_in_unsafe

(* Remove interpreted symbols, i.e remove the variables
   that have a name that is a function.
*)
let remove_interpreted_symbols (vars : VarSet.t) =
  VarSet.filter
    (fun v -> uninterpeted v.vname)
    vars

(* Returns true if the expression is a function name. *)
let is_exp_function ef =
  match ef with
  | Cil.Lval (Cil.Var vi, _) ->
    let fname = vi.Cil.vname in
    let ty = vi.Cil.vtype in
    uninterpeted fname, Some vi, ty

  | _ -> false,  None , Cil.typeOf ef

(**
   Generate a FnVar expression from a variable, with possible offsets
   for arrays. Checks first if the name of the variable is a predefined
   constant.
*)
let mkVar ?(offsets = []) vi =
  List.fold_left
    (fun fnlvar offset -> FnArray (fnlvar, offset))
    (FnVariable vi)
    offsets

(**
   Create an expression from a varinfo and offsets, possibly returning
   a constant if the name of the variable is a predefined constant.
*)
let mkVarExpr ?(offsets = []) vi =
  match c_constant vi.vname with
  | Some c -> FnConst c
  | None -> FnVar (mkVar ~offsets:offsets vi)


let bind_state ?(prefix="") ~state_rec:state_var ~members:vs =
  let vars = VarSet.elements vs in
  List.map
    (fun v ->
       (FnVariable {v with vname=prefix^v.vname},
        FnRecordMember(mkVarExpr state_var, v.vname)))
    vars



let is_vi fnlv vi = maybe_apply_default (fun x -> vi = x) (vi_of fnlv) false


let is_reserved_name s = not (uninterpeted s)


let rec var_of_fnvar fnvar =
  match fnvar with
  | FnVariable v -> v
  | FnArray (v, e) -> var_of_fnvar v

(** Get the dependency length of an array variable. We assume very
    simple offset expressions.*)

let rec fnArray_dep_len e =
  match e with
  | FnVar v ->
    (match v with FnVariable vi -> 1
                | FnArray (v, e') -> fnArray_dep_len e')

  | FnConst (CInt i) -> i + 1
  | FnConst (CInt64 i) -> (Int64.to_int i) + 1
  | FnBinop (op, e1, e2) when op = Plus || op = Minus ->
    fnArray_dep_len e1 + fnArray_dep_len e2
  | _ ->
    eprintf "ERROR : cannot guess min array length of expression.@.";
    failwith "Unsupported array offset expression."

(** Remove interpreted symbols from a set of vars *)
let remove_reserved_vars vs =
  VS.filter
    (fun vi ->
       (if uninterpeted vi.Cil.vname then
          (if !debug then printf "@.Removing %s." vi.Cil.vname; true)
        else false)) vs


(** When an expression is supposed to be a constant *)
let force_constant expr =
  match expr with
  | FnConst c -> c
  | _ -> failwith "Force_constant failure."


let mkOp ?(t = Unit) vi argl =
  let fname = vi.vname in
  match symb_unop_of_fname fname with
  | Some unop ->
    FnUnop (unop, List.hd argl)
  | None ->
    begin
      match symb_binop_of_fname fname with
      | Some binop ->
        FnBinop (binop, List.hd argl, List.nth argl 2)
      | None ->
        FnApp (t, Some vi, argl)
    end


(* Convert Cil Varinfo to variable *)

let var_of_vi vi =
  let var =
    {
      vname = vi.Cil.vname;
      vinit = None;
      vtype = type_of_ciltyp vi.Cil.vtype;
      vid = vi.Cil.vid;
      vistmp = vi.Cil.vistmp;
    }
  in
  register_fnv var;
  var

let varset_of_vs vs =
  VarSet.of_list (List.map var_of_vi (VS.elements vs))

(* And vice versa *)

let cil_varinfo var =
  try
    find_vi_name_id var.vname var.vid
  with Not_found ->
  match ciltyp_of_symb_type var.vtype with
  | Some vt ->
    let vi = Cil.makeVarinfo false var.vname vt in
    register_vi vi;
    vi

  | None ->
    failhere __FILE__ "cil_varinfo" "Couldn't convert type."

(* Compare variables by comparing the variable id of their varinfo. *)
let rec cmpVar fnlvar1 fnlvar2 =
  match fnlvar1, fnlvar2 with
  | FnVariable vi, FnVariable vi' -> compare vi.vid vi'.vid
  | FnArray (fnlv1, _), FnArray (fnlv2, _) ->
    cmpVar fnlv1 fnlv2
  | FnArray _ , _ -> 1
  | _ , FnArray _ -> -1


(* ---------------------------- 4 - RECURSORS -------------------------------*)


type 'a recursor=
  {
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
let rec_expr
    (join : 'a -> 'a -> 'a)
    (init : 'a)
    (case : fnExpr -> bool)
    (case_handler : (fnExpr -> 'a) -> fnExpr -> 'a)
    (const_handler: constants -> 'a)
    (var_handler : fnLVar -> 'a)
    (expre : fnExpr) : 'a =

  let rec recurse_aux =
    function
    | e when case e -> case_handler recurse_aux e
    | FnVar v -> var_handler v
    | FnConst c -> const_handler c

    | FnBinop (_, e1, e2) ->
      join (recurse_aux e1) (recurse_aux e2)

    | FnCastE (_, e)
    | FnAlignofE e
    | FnAddrof e
    | FnSizeofE e | FnStartOf e
    | FnUnop (_, e) -> recurse_aux e

    | FnCond (c, e1, e2) ->
      join (join (recurse_aux c) (recurse_aux e1)) (recurse_aux e2)

    | FnApp (_, _, el) ->
      List.fold_left (fun a e -> join a (recurse_aux e)) init el

    | FnFun letin
    | FnRec (_, _, (_, letin)) -> recurse_aux letin


    | FnLetExpr velist ->
      List.fold_left (fun acc (v, e) -> join acc (recurse_aux e))
        init velist

    | FnLetIn (velist, letin) ->
      let in_aux = recurse_aux letin in
      List.fold_left
        (fun acc (v, e) -> join acc (recurse_aux e)) in_aux velist

    | _ -> init
  in
  recurse_aux expre

let rec_expr2 (r : 'a recursor) =
  rec_expr r.join r.init r.case r.on_case r.on_const r.on_var


let max_min_test =
  { join = (fun a b -> a || b);
    init = false;
    case = (fun e ->
        match e with FnBinop (op, _, _) -> op = Max || op = Min | _ -> false);
    on_case = (fun f e ->
        match e with FnBinop (op, _, _) -> op = Max || op = Min | _ -> false);
    on_const = (fun e -> false);
    on_var = (fun e -> true);
  }


(** Another recursion helper : a syntax tree tranformer *)
type  ast_transformer =
  {
    case : fnExpr -> bool;
    on_case : (fnExpr -> fnExpr) -> fnExpr -> fnExpr;
    on_const : constants -> constants;
    on_var : fnLVar -> fnLVar;
  }

let transform_expr
    (case : fnExpr -> bool)
    (case_handler : (fnExpr -> fnExpr) -> fnExpr -> fnExpr)
    (const_handler: constants -> constants)
    (var_handler : fnLVar -> fnLVar)
    (expre : fnExpr) : 'a =

  let rec recurse_aux expr =
    match expr with
    | e when case e ->
      case_handler recurse_aux e

    | FnVar v -> FnVar (var_handler v)

    | FnConst c -> FnConst (const_handler c)

    | FnBinop (op, e1, e2) ->
      FnBinop (op, (recurse_aux e1), (recurse_aux e2))

    | FnUnop (op, e) -> FnUnop (op, recurse_aux e)

    | FnApp (a, b, el) ->
      FnApp (a, b, List.map (fun e -> recurse_aux e) el)

    | FnFun letin -> FnFun (recurse_aux letin)
    | FnRec (igu, (inner_state, init_inner_state), (s, letin)) ->
      FnRec (igu, (inner_state, recurse_aux init_inner_state), (s, recurse_aux letin))

    | FnCond (c, l1, l2) ->
      FnCond (recurse_aux c, recurse_aux l1, recurse_aux l2)

    | FnLetExpr velist ->
      FnLetExpr (List.map (fun (v, e) -> (v, recurse_aux e)) velist)

    | FnLetIn (velist, letin) ->
      let in_aux = recurse_aux letin in
      FnLetIn (List.map (fun (v, e) -> (v, recurse_aux e)) velist, in_aux)

    | FnHoleL(t, v, cs, e) -> FnHoleL(t, v, cs, recurse_aux e)

    | FnHoleR(t, cs, e) -> FnHoleR(t, cs, recurse_aux e)

    | FnChoice el -> FnChoice (List.map recurse_aux el)

    | FnVector ea -> FnVector (List.map recurse_aux ea)

    | FnRecord(t, el) -> FnRecord(t, List.map recurse_aux el)

    | FnRecordMember(e, s) -> FnRecordMember(recurse_aux e, s)

    | FnArraySet(a, i, e) -> FnArraySet(recurse_aux a, recurse_aux i, recurse_aux e)

    | FnCastE (t, e) -> FnCastE (t, recurse_aux e)
    | FnAlignofE e -> FnAlignofE (recurse_aux e)
    | FnAddrof e -> FnAddrof (recurse_aux e)
    | FnSizeofE e -> FnSizeofE (recurse_aux e)
    | FnStartOf e -> FnStartOf (recurse_aux e)
    | FnSizeof _ | FnAlignof _ | FnAddrofLabel _ | FnSizeofStr _ -> expr
  in
  recurse_aux expre

let transform_expr2 tr =
  transform_expr tr.case tr.on_case tr.on_const tr.on_var

(** Transformation with extra boolean argument *)
let transform_expr_flag
    (top : bool)
    (case : bool -> fnExpr -> bool)
    (case_handler : bool-> (bool -> fnExpr -> fnExpr) -> fnExpr -> fnExpr)
    (const_handler: bool -> constants -> constants)
    (var_handler : bool -> fnLVar -> fnLVar)
    (expre : fnExpr) : 'a =

  let rec recurse_aux flag =
    function
    | e when case flag e ->
      case_handler flag recurse_aux e

    | FnVar v -> FnVar(var_handler flag v)
    | FnConst c -> FnConst (const_handler flag c)

    | FnBinop (op, e1, e2) ->
      FnBinop (op, (recurse_aux flag e1), (recurse_aux flag e2))

    | FnCastE (t, e) -> FnCastE (t, recurse_aux flag e)
    | FnAlignofE e -> FnAlignofE (recurse_aux flag e)
    | FnAddrof e -> FnAddrof (recurse_aux flag e)
    | FnSizeofE e -> FnSizeofE (recurse_aux flag e)
    | FnStartOf e -> FnStartOf (recurse_aux flag e)
    | FnUnop (op, e) -> FnUnop (op, recurse_aux flag e)

    | FnApp (a, b, el) ->
      FnApp (a, b, List.map (fun e -> recurse_aux flag e) el)

    | FnFun letin -> FnFun (recurse_aux flag letin)
    | FnRec (igu, istate, (s, letin)) -> FnRec (igu, istate, (s, recurse_aux flag letin))

    | FnCond (c, l1, l2) ->
      FnCond (recurse_aux flag c, recurse_aux flag l1, recurse_aux flag l2)

    | FnLetExpr velist ->
      FnLetExpr (List.map (fun (v, e) -> (v, recurse_aux flag e)) velist)

    | FnLetIn (velist, letin) ->
      let in_aux = recurse_aux flag letin in
      FnLetIn (List.map (fun (v, e) ->
          (v, (recurse_aux flag e))) velist, in_aux)

    | e -> e
  in
  recurse_aux top expre



type ast_var_transformer =
  {
    ctx : fnLVar ref;
    case : fnExpr -> bool;
    on_case : (fnExpr -> fnExpr) -> fnExpr -> fnExpr;
    on_const : constants -> constants;
    on_var : fnLVar -> fnLVar;
  }


let transform_bindings (tr : ast_var_transformer) =
  let rec recurse_aux =
    function
    | e when tr.case e ->
      tr.on_case recurse_aux e

    | FnVar v -> FnVar (tr.on_var v)
    | FnRecordMember (rv, s) -> FnRecordMember (recurse_aux rv, s)
    | FnConst c -> FnConst (tr.on_const c)

    | FnBinop (op, e1, e2) ->
      FnBinop (op, (recurse_aux e1), (recurse_aux e2))

    | FnCastE (t, e) -> FnCastE (t, recurse_aux e)
    | FnAlignofE e -> FnAlignofE (recurse_aux e)
    | FnAddrof e -> FnAddrof (recurse_aux e)
    | FnSizeofE e -> FnSizeofE (recurse_aux e)
    | FnStartOf e -> FnStartOf (recurse_aux e)
    | FnUnop (op, e) -> FnUnop (op, recurse_aux e)

    | FnApp (a, b, el) ->
      FnApp (a, b, List.map (fun e -> recurse_aux e) el)

    | FnFun letin -> FnFun (recurse_aux letin)
    | FnRec (igu, (inner_state, init_inner_state), (s, letin)) ->
      FnRec (igu, (inner_state, recurse_aux init_inner_state), (s, recurse_aux letin))

    | FnCond (c, l1, l2) ->
      FnCond (recurse_aux c, recurse_aux l1, recurse_aux l2)

    | FnLetExpr velist ->
      FnLetExpr (List.map (fun (v, e) -> tr.ctx := v; (v, recurse_aux e)) velist)

    | FnLetIn (velist, letin) ->
      let in_aux = recurse_aux letin in
      FnLetIn (List.map (fun (v, e) -> tr.ctx := v; (v, (recurse_aux e))) velist, in_aux)

    | e -> e
  in
  recurse_aux


(** An application of a function transformer : replace
    expression to_replace by expression by.
*)
let rec replace_expression ?(in_subscripts = false)
    ~to_replace:tr ~by:b ~ine:exp=
  let case e = (e = tr) in
  let case_handler rfunc e = b in
  let const_handler c = c in
  let rec var_handler v =
    if in_subscripts then
      match v with
      | FnArray (v, e) ->
        FnArray (var_handler v,
                 replace_expression ~in_subscripts:true ~to_replace:tr ~by:b
                   ~ine:e)
      | _ -> v
    else
      v
  in
  transform_expr case case_handler const_handler var_handler exp


let to_rec_completions e =
  transform_expr2 {
    case = (fun e -> match e with FnHoleL _ | FnHoleR _ -> true | _ -> false);
    on_case =
      (fun f e ->
         match e with
         | FnHoleL(ht, var, cst, e') -> FnHoleL(ht, var, CS._LRorRec cst, e')
         | FnHoleR(ht, cst, e') -> FnHoleR(ht, CS._LRorRec cst, e')
         | _ -> f e);
    on_var = identity;
    on_const = identity
  } e
(**
   Replace expression n time. Returns a list of expressions, with all
   the possible combinations.
*)
let rec replace_many ?(in_subscripts = false)
    ~to_replace:tr ~by:b ~ine:expr ~ntimes:n =
  (* Count how many expresions have to be replace, and then using a mutable
     counter replace expressions depending on counter. For each possible
     combination, give the indexes that have to be replaced. *)
  let num_occ =
    rec_expr2
      {
        init = 0;
        join = (fun a b -> a + b);
        case = (fun e -> e = tr);
        on_case = (fun e f -> 1);
        on_var = (fun v -> 0);
        on_const = (fun c -> 0);
      } expr
  in
  let repl_indexed il =
    let cntr = ref 0 in
    transform_expr2
      {
        case = (fun e -> e = tr);
        on_var = (fun v -> v);
        on_case = (fun f e -> incr cntr; if List.mem !cntr il then b else e);
        on_const = (fun c -> c)
      }
      expr
  in
  if num_occ <= 0 then [expr] else
    let index_to_repl = k_combinations n (1 -- num_occ) in
    List.map repl_indexed index_to_repl



let rec apply_substutions subs e =
  let case e =
    match e with
    | FnVar (FnVariable vi) -> true
    | _ -> false
  in
  let case_handler rfunc e =
    match e with
    | FnVar (FnVariable vi) ->
      (try IM.find vi.vid subs with Not_found -> e)
    | _ -> rfunc e
  in
  let const_handler c = c in
  let var_handler v = v in
  transform_expr case case_handler const_handler var_handler e

let rec replace_expression_in_subscripts
    ~to_replace:tr ~by:b ~ine:exp=
  let case e = false in
  let case_handler rfunc e = e in
  let const_handler c = c in
  let var_handler v =
    match v with
    | FnArray (v, e) ->
      FnArray (v, replace_expression ~in_subscripts:true ~to_replace:tr ~by:b ~ine:e)
    | _ -> v
  in
  transform_expr case case_handler const_handler var_handler exp

let replace_all_subs ~tr:el ~by:oe ~ine:e =
  List.fold_left2
    (fun ne tr b ->
       replace_expression_in_subscripts
         ~to_replace:tr ~by:b ~ine:ne)
    e el oe

let rec fn_uses vs expr =
  let join a b = a || b in
  let case e = false in
  let case_handler f e =  false in
  let const_handler c = false in
  let var_handler v =
    try VarSet.mem (check_option (vi_of v)) vs with Not_found -> false
  in rec_expr join false case case_handler const_handler var_handler expr

(** Operator complexity of a function or an expression *)
let optype_rec =
  { join = join_optypes;
    init = NotNum;
    case =
      (fun e ->
         match e with
         | FnUnop (op, e) -> true
         | FnBinop (op, e1, e2) -> true
         | _ -> false);
    on_case =
      (fun f e ->
         match e with
         | FnUnop (op, e) ->
           join_optypes (optype_of_unop op) (f e)
         | FnBinop (op, e1, e2) ->
           join_optypes (join_optypes (optype_of_binop op) (f e1)) (f e2)
         | _ -> NotNum);
    on_const = (fun _ -> NotNum);
    on_var = (fun _ -> NotNum);}


let analyze_optype (e : fnExpr) : operator_type = rec_expr2 optype_rec e


(** Compose a function by adding new assignments *)
let rec remove_id_binding func =
  let aux_rem_from_list el =
    List.filter
      (fun (v,e) -> not (e = FnVar v)) el
  in
  match func with
  | FnLetExpr el -> FnLetExpr (aux_rem_from_list el)
  | FnLetIn (el, c) -> FnLetIn (aux_rem_from_list el, remove_id_binding c)
  | _ -> func

let rec compose func1 func2 =
  match func1 with
  | FnLetExpr el -> FnLetIn (el, func2)
  | FnLetIn (el, c) -> FnLetIn (el, compose c func2)
  | _ -> func1

let compose_head assignments func =
  match assignments with
  | [] -> func
  | _ -> FnLetIn (assignments, func)

let rec compose_tail assignments func =
  match assignments with
  | [] -> func
  | _ ->
    match func with
    | FnLetExpr el ->
      FnLetIn (el, FnLetExpr assignments)
    | FnLetIn (el, l) -> FnLetIn (el, compose_tail assignments l)
    | _ -> func

let complete_with_state stv el =
  let emap =
    List.fold_left
      (fun map (v,e) ->
         let vi = check_option (vi_of v) in
         IM.add vi.vid (v, e) map)
      IM.empty el
  in
  let map' =
    VarSet.fold
      (fun vi map ->
         if IM.mem vi.vid map then map
         else IM.add vi.vid (mkVar vi, mkVarExpr vi) map)
      stv emap
  in
  let _, velist = ListTools.unpair (IM.bindings map') in
  velist


let rec complete_final_state stv func =
  match func with
  | FnLetExpr el -> FnLetExpr (complete_with_state stv el)
  | FnLetIn (el, l) -> FnLetIn (el, complete_final_state stv l)
  | _ -> func


let rec used_in_fnexpr e : VarSet.t =
  let join = VarSet.union in
  let init = VarSet.empty in
  let case e = false in
  let case_h f e = VarSet.empty in
  let rec var_handler v =
    match v with
    | FnVariable vi -> VarSet.singleton vi
    | FnArray (v0, e) ->
      VarSet.union (var_handler v0) (used_in_fnexpr e)
  in
  let const_handler c = VarSet.empty in
  rec_expr join init case case_h const_handler var_handler e


let rec used_in_fnlet  =
  function
  | FnLetIn (ve_list, letin) ->
    let bs1, us1 = (used_in_fnlet letin) in
    let bs2, us2 = (used_in_assignments ve_list) in
    (VarSet.union bs1 bs2, VarSet.union us1 us2)
  | FnLetExpr ve_list ->
    used_in_assignments ve_list
  | e -> (VarSet.empty, used_in_fnexpr e)

and used_in_assignments ve_list =
  List.fold_left
    (fun (bind_set, use_set) (v, e) ->
       (VarSet.union bind_set
          (match vi_of v with
           | Some vi -> VarSet.singleton vi
           | None -> VarSet.empty),
        VarSet.union use_set (used_in_fnexpr e)))
    (VarSet.empty, VarSet.empty) ve_list


(** ------------------------ 5 - SCHEME <-> FUNC -------------------------- *)


(** Translate basic scheme to the Func expressions
    @param env a mapping from variable ids to varinfos.
*)
let errmsg_unexpected_fnlet unex_let =
  (fprintf str_formatter "Expected a translated expression,\
                          received for tranlsation @; %a @."
     RAst.pp_expr unex_let;
   flush_str_formatter ())

let errmsg_unexpected_expr ex_type unex_expr =
  (fprintf str_formatter "Expected a %s ,\
                          received for tranlsation @; %a @."
     ex_type RAst.pp_expr unex_expr;
   flush_str_formatter ())


type join_translation_info = {
  mutable initial_vars : VarSet.t;
  mutable initial_state_vars : VarSet.t;
  mutable used_vars : fnV SH.t;
  mutable used_state_vars : VarSet.t;
  initial_state_right : fnV IH.t;
  initial_state_left: fnV IH.t;
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

let get_unop_of_scm (op : RAst.op) : symb_unop=
  match op with
  | Not -> Not
  | _ -> failwith "Scheme unary operator not supported"

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
let scm_register s =
  let pure_varname, is_class_member, is_right_state_mem =
    is_right_state_varname s in
  let varinfo : fnV =
    try
      SH.find join_info.used_vars pure_varname
    with Not_found ->
      begin
        let newly_used_vi =
          try
            VarSet.find_by_name join_info.initial_vars pure_varname
          with
          | Not_found ->
            mkFnVar pure_varname Bottom
        in
        SH.add join_info.used_vars pure_varname newly_used_vi;
        newly_used_vi
      end
  in
  {varinfo with vname = s}

let hole_var_name = "??_hole"
let hole_var = mkFnVar hole_var_name Bottom

let from_accessor a s =
  if is_struct_accessor a then
    let member_name = (Str.split (Str.regexp "-") a) >> 1 in
    let state =
      try
        find_var_name s
      with Not_found -> failhere __FILE__ "from_accessor" ("State not found : "^s)
    in
    FnRecordMember(mkVarExpr state, member_name)
  else
    let msg =
      fprintf str_formatter "Expected a struct accessor received %s" a;
      flush_str_formatter ()
    in
    failhere __FILE__ "from_accessor" msg



let remove_hole_vars (expr: fnExpr) : fnExpr =
  let rec aux_rem_h t e =
    match e with
    | FnVar (FnVariable v) when v = hole_var ->
      (match t with
       | Num -> FnConst (CInt 0)
       | _ -> FnConst (CBool true))

    | FnBinop (op, e1, e2) ->
      let tdown = type_of_binop_args op in
      FnBinop (op, aux_rem_h tdown e1, aux_rem_h tdown e2)

    | FnUnop (op, e0) ->
      let tdown = type_of_unop_args op in
      FnUnop (op, aux_rem_h tdown e0)

    | FnCond (c, e1, e2) ->
      FnCond (aux_rem_h Boolean c, aux_rem_h t e1, aux_rem_h t e2)

    | FnApp (t, vo, el) ->
      FnApp (t, vo, List.map (fun e -> aux_rem_h Unit e) el)

    | FnLetExpr ve_list ->
      FnLetExpr (List.map (fun (v, e) ->  (v, aux_rem_h Unit  e)) ve_list)
    | FnLetIn (ve_list, letin) ->
      FnLetIn ((List.map (fun (v, e) ->  (v, aux_rem_h Unit e)) ve_list),
               aux_rem_h Unit letin)
    | e -> e
  in
  aux_rem_h Unit expr


let rec scm_to_fn (scm : RAst.expr) : fnExpr =
  let unwrap_fun_e e =
    match e with
    | Fun_e (il, e') -> e'
    | e -> e
  in
  let get_fun_state e =
        match e with
    | Fun_e (il, e') -> find_var_name (il >> 0)
    | _ -> failwith "get_fun_state only on fun_e"
  in
  let rec translate (scm : RAst.expr) : fnExpr =
    try
      match scm with
      | Int_e i -> FnConst (CInt i)
      | Float_e f -> FnConst (CReal f)
      | Str_e s -> FnConst (CString s)
      | Bool_e b -> FnConst (CBool b)
      | Id_e id ->
        (match id with
         | "??" -> FnVar (FnVariable hole_var)
         | _ ->
           (let vi = scm_register id in
            FnVar (FnVariable vi)))
      | Nil_e -> FnConst (CNil)

      | Binop_e (op, e1, e2) ->
        let e1' = translate  e1 in
        let e2' = translate  e2 in
        FnBinop (get_binop_of_scm op, e1', e2')

      | Unop_e (op, e) ->
        let e' = translate  e in
        FnUnop (get_unop_of_scm op, e')

      | Cons_e (x, y)-> failwith "Cons not supported"

      | Let_e (bindings, e2)
      | Letrec_e (bindings, e2) ->
        let fn_bindings = List.map
            (fun (ids, e) ->
               let  exp = translate e in
               let vi = scm_register ids in
               (FnVariable vi, exp))
            bindings
        in
        let fn_let = translate  e2 in
        FnLetIn (fn_bindings, fn_let)

      | If_e (c, e1, e2) ->
        let cond = translate  c in
        let le1 = translate  e1 in
        let le2 = translate  e2 in
        FnCond (cond, le1, le2)

      | Apply_e (e, arglist) ->
        (match e with
         | Id_e s ->
           (match s with
            | "list-ref" ->
              FnVar (to_array_var arglist)

            | "LoopFunc" ->
              (if List.length arglist = 5 then
                 let init = translate (unwrap_fun_e (arglist >> 0)) in
                 let guard = translate (unwrap_fun_e (arglist >> 1)) in
                 let update = translate (unwrap_fun_e (arglist >> 2)) in
                 let __s = get_fun_state (arglist >> 4) in
                 let stv =
                   match __s.vtype with
                   | Record name_type_list ->
                     VarSet.of_list (List.map (fun (n,t) -> find_var_name n) name_type_list)
                   | _ -> failhere __FILE__ "translate scm" "Expected a record type."
                 in
                 let stv_init =
                   match arglist >> 3 with
                   | Apply_e (e, inits) ->
                     FnRecord(__s.vtype, List.map translate inits)
                   | _ -> failhere __FILE__ "translate scm" "Expected a record expression."
                 in
                 FnRec ((init, guard, update),
                        (stv, stv_init),
                        (__s, translate (unwrap_fun_e (arglist >> 4)))
                       )
               else
                 failhere __FILE__ "scm_to_fn" "LoopFunc macro with more than 5 args."
              )

            | "make-list" ->
              let ln =
                match List.hd arglist with
                | Int_e i -> i
                | _ -> failhere __FILE__ __LOC__ "Parsed make-list without length integer."
              in
              let v = translate (arglist >> 1) in
              begin
                match v with
                | FnConst c ->
                  FnConst(CArrayInit(ln, c))
                | _ ->
                  FnVector(ListTools.init ln (fun i -> v))
              end

            | a when is_struct_accessor s ->
              (match arglist with
               | [Id_e s] -> from_accessor a s
               | _ -> failhere __FILE__ __LOC__ "Bad accessor")

            | a when is_name_of_struct s ->
              rosette_state_struct_to_fnlet s arglist

            | "identity" ->
              translate (arglist >> 0)

            | "list-set" ->
              let a = translate (arglist >> 0) in
              let i = translate (arglist >> 1) in
              let e = translate (arglist >> 2) in
              FnArraySet(a,i,e)

            | _ ->
              to_fun_app e arglist)

         | _ ->
           translate e)


      | Fun_e (il, e) ->
        let es = pp_space_sep_list (fun fmt s -> fprintf fmt "%s" s)
            str_formatter il; flush_str_formatter () in
        failhere __FILE__ "scm_to_fn" ("Fun_e : Not supported, ids: "^es)

      | Def_e _ ->
        failhere __FILE__ "scm_to_fn" "Def_e : definition not supported."

      | Defrec_e _ ->
        failhere __FILE__ "scm_to_fn" "Defrec_e : definitions not supported."

      | Delayed_e _ | Forced_e _ ->
        failhere __FILE__ "scm_to_fn" "Delayed_e or Forced_e not suppported."

    with Not_found ->
      eprintf "expression : %a" pp_expr scm;
      failwith "Variable name not found in current environment."
  in
  let fne = translate scm in
  remove_hole_vars fne

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
    FnLetExpr (ListTools.pair (List.map (fun vi -> FnVariable vi) stv_vars_list)
                 fn_expr_list)
  with Invalid_argument s ->
    (* Might be an inner state struct. *)
    (try
       FnRecord(Record(get_struct sname), fn_expr_list)
     with Not_found ->
       eprintf "FAILURE :@\n\
                Failed to translate state in list of bindings, got %i state \
                variables and state was %i long.@\n\
                ---> Did you initialize the join_info before using scm_to_fn ?"
         (VarSet.cardinal join_info.initial_state_vars)
         (List.length fn_expr_list);
       failwith "Failure in rosette_state_struct_to_fnlet.")

and to_expression_list scm_expr_list =
  List.map scm_to_fn scm_expr_list

and to_array_var scm_expr_list =
  let array_varinfo =
    match scm_expr_list >> 0 with
    | Id_e varname -> scm_register varname
    | e -> raise (Failure (errmsg_unexpected_expr "identifier" e))
  in
  let offset_list = to_expression_list (List.tl scm_expr_list) in
  mkVar ~offsets:offset_list array_varinfo

and to_fun_app ?(typ = Bottom) fun_expr scm_expr_list =
  let fun_vi =
    match fun_expr with
    | Id_e fun_name ->
      scm_register fun_name
    | _ -> raise (Failure (errmsg_unexpected_expr "identifier" fun_expr))
  in
  let args = to_expression_list scm_expr_list in
  FnApp (Bottom, Some fun_vi, args)

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
           (fun new_subs (v,e) ->
              try
                let vi = co (vi_of v)  in
                IM.add vi.vid (apply_substutions subs_copy e) new_subs
              with Failure s -> new_subs)
           subs ve_list)

    | FnLetExpr ve_list ->
      let subs_copy = subs in
      let final_subs =
        (List.fold_left
           (fun new_subs (v,e) ->
              try
                let vi = co (vi_of v)  in
                IM.add vi.vid (apply_substutions subs e) new_subs
              with Failure s -> new_subs)
           subs_copy ve_list)
      in
      FnLetExpr
        (IM.fold
           (fun vid e ve_list ->
              ve_list@[(FnVariable (VarSet.find_by_id vs vid), e)])
           final_subs [])
    | _ -> failhere __FILE__ "force_flat" "Not a proper function."
  in
  let start_sub =
    VarSet.fold
      (fun vi subs -> IM.add vi.vid (FnVar (FnVariable vi)) subs)
      vs
      IM.empty
  in
  force_aux fnlet start_sub



(** ------------------------ 6 - EXPRESSION SETS -----------------------------*)

module ES = Set.Make (
  struct
    let compare = Pervasives.compare
    type t = fnExpr
  end)


(** Context for expression analysis *)
type context = {
  state_vars : VarSet.t;
  index_vars : VarSet.t;
  used_vars : VarSet.t;
  all_vars : VarSet.t;
  costly_exprs : ES.t
}

let mk_ctx vs stv = {
  state_vars = stv;
  index_vars = VarSet.empty;
  used_vars = VarSet.diff stv vs;
  all_vars = vs;
  costly_exprs = ES.empty
}


let ctx_update_vsets ctx vs =
  let new_allvs = VarSet.union ctx.all_vars vs in
  let new_usedvs = VarSet.union ctx.used_vars vs in
  let new_stvs = VarSet.union ctx.state_vars vs in
  { ctx with
    state_vars = new_stvs;
    used_vars = new_usedvs;
    all_vars =  new_allvs }

let ctx_add_cexp ctx cexp =
  {ctx with costly_exprs = cexp}


(** ------------------- 7 - INDEX VARIABLES MANAGEMENT ----------------------*)
(** Create and manage variables for index boundaries *)


(* Extract boundary variables "n" from func information *)
let rec get_loop_bound_var (se : fnExpr) : fnExpr option =
  match se with
  | FnBinop (Lt, _, en) -> Some en
  | FnBinop (Le, _, ene) -> Some ene
  | _ -> None


(** Really not here to last ... must find a better way to differentiate
    the expressions. *)
let is_prefix_or_suffix vi expr =
  match expr with
  | FnVar (FnArray (_, _)) -> true
  | _ -> false


(* ------------------------ 8 - STRUCT UTILS ----------------------------*)

type sigu = VarSet.t * (fnExpr * fnExpr * fnExpr)

type func_dec =
  {
    fvar : fnV;
    fformals : fnV list;
    flocals : fnV list;
  }

type prob_rep =
  {
    id : int;
    host_function : func_dec;
    loop_name : string;
    scontext : context;
    min_input_size : int;
    uses_global_bound : bool;
    main_loop_body : fnExpr;
    loop_body_versions : fnExpr SH.t;
    join_sketch : fnExpr * fnExpr -> fnExpr;
    memless_sketch : fnExpr * fnExpr ->  fnExpr;
    join_solution : fnExpr;
    memless_solution : fnExpr;
    init_values : RAst.expr IM.t;
    identity_values : constants IM.t;
    func_igu : sigu;
    reaching_consts : fnExpr IM.t;
    inner_functions : prob_rep list;
  }

let mkFuncDec fndc =
  {
    fvar = var_of_vi fndc.Cil.svar;
    fformals = List.map var_of_vi fndc.Cil.sformals;
    flocals = List.map var_of_vi fndc.Cil.slocals;
  }

let get_index_init problem =
  let idx, (i, g, u) = problem.func_igu in i

let get_index_update problem =
  let idx, (i, g, u) = problem.func_igu in u

let get_index_varset problem =
  let idx, (i, g, u) = problem.func_igu in idx

let get_index_guard problem =
  let idx, (i, g, u) = problem.func_igu in g

let get_init_value problem vi =
  try IM.find vi.vid problem.reaching_consts
  with Not_found ->
    scm_to_fn (IM.find vi.vid problem.init_values)

let get_loop_bound problem =
  get_loop_bound_var (get_index_guard problem)

let get_bounds problem =
  let bvar = VarSet.max_elt (get_index_varset problem) in
  try
    find_var_name (bvar.vname^"_start"),
    find_var_name (bvar.vname^"_end")
  with Not_found ->
    mkFnVar (bvar.vname^"_start") bvar.vtype,
    mkFnVar (bvar.vname^"_end") bvar.vtype

(* ----------------------- 9 - CONVERSION TO CIL  ----------------------------*)

(** Includes passes to transform the code into an appropriate form *)

let rec pass_remove_special_ops e =
  (transform_expr
     (fun e -> match e with FnBinop _ -> true
                          | FnApp _ -> true
                          | _ -> false)
     (fun rfun e ->
        match e with
        | FnBinop (op, e1, e2) ->
          let e1' = rfun e1 in let e2' = rfun e2 in
          (match op with
           | Max ->
             FnCond (FnBinop(Gt, e1', e2'), e1', e2')

           | Min ->
             FnCond (FnBinop(Lt, e1', e2'), e1', e2')

           | Nand ->
             FnUnop (Not, FnBinop (And, e1', e2'))

           | Neq ->
             FnUnop (Not, FnBinop (Eq, e1, e2))

           | _ -> FnBinop (op, e1', e2'))

        | FnApp (st, vo, args) ->
          let args' = List.map rfun args in
          (if List.length args' >= 1 then
             (** Might be a binary operator ... *)
             (let e1 = args' >> 0 in
              match vo with
              | Some var ->
                (match String.lowercase var.vname with
                 | "max" ->
                   let e2 = args' >> 1 in
                   FnCond (FnBinop(Gt, e1, e2), e1, e2)
                 | "min" ->
                   let e2 = args' >> 1 in
                   FnCond (FnBinop(Lt, e1, e2), e1, e2)
                 | "add1" ->
                   FnBinop (Plus, e1, FnConst (CInt 1))
                 | "sub1" ->
                   FnBinop (Minus, e1, FnConst (CInt 1))
                 | _ -> FnApp(st, vo, args'))
              | None ->
                FnApp(st, vo, args'))
           else
             FnApp(st, vo, args'))

        | FnLetIn (ve_list , letin) ->
          FnLetIn (List.map (fun (v, e) ->
              (v, pass_remove_special_ops e)) ve_list,
                   pass_remove_special_ops letin)
        | FnLetExpr ve_list ->
          FnLetExpr (List.map (fun (v, e) ->
              (v, pass_remove_special_ops e)) ve_list)

        | _ -> failwith "Bad rec case.") identity identity) e


let rec pass_sequentialize fnlet =
  let rec reorganize ve_list let_queue =
    (** A variable should be only bound once in a binding group, therefore
        we can identify a binding only by the variables it binds to.
        We supports only scalar types ! n *)
    let modified_vars, vid_to_expr, depends_graph_unpure =
      List.fold_left
        (fun (modified_set, expr_map, dep_graph) (v, e) ->
           match e with
           | FnVar v' when v = v' ->
             modified_set, expr_map, dep_graph (* Identity binding *)
           | _ ->
             let vi =
               try check_option (vi_of v)
               with Failure s ->  failwith "Non-scalar type unsupported"
             in
             let expr_depends = used_in_fnexpr e in
             (VarSet.add vi modified_set,
              IM.add vi.vid e expr_map,
              IM.add vi.vid expr_depends dep_graph))
        (VarSet.empty, IM.empty, IM.empty) ve_list
    in
    (* let depends_graph = IM.map (fun deps -> VarSet.inter deps modified_vars) *)
    (*     depends_graph_unpure *)
    (* in *)
    (** We need to implement here the algorithm described in :
        http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf *)
    let statement_order = VarSet.vids_of_vs modified_vars in
    List.fold_left
      (fun let_bindings vid ->
         FnLetIn ([FnVariable (VarSet.find_by_id modified_vars vid),
                   IM.find vid vid_to_expr], let_bindings))
      let_queue statement_order
      (** Analyze dependencies to produce bindings ordered such that
          the sequence of bindings yields to the same state as the functional
          version where all expressions are evaluated in one step. *)

  in

  let rec sequentialize_parallel_moves =
    function
    | FnLetIn (ve_list, letin) ->
      reorganize ve_list (pass_sequentialize letin)
    | FnLetExpr ve_list ->
      reorganize ve_list (FnLetExpr [])
    | e -> e
  in
  let rec remove_empty_lets =
    function
    | FnLetIn (ve_list, letin) ->
      (match remove_empty_lets letin with
       | Some let_tail ->
         (match ve_list with
          | [] -> Some let_tail
          | _ -> Some (FnLetIn (ve_list, let_tail)))
       | None ->
         (match ve_list with
          | [] -> None
          | _ -> Some (FnLetExpr ve_list)))

    | FnLetExpr ve_list ->
      (match ve_list with
       | [] -> None
       | _ -> Some (FnLetExpr ve_list))
    | e -> Some e
  in
  match remove_empty_lets (sequentialize_parallel_moves fnlet) with
  | Some fnlet -> fnlet
  | None -> FnLetExpr []


let fn_for_c fnlet =
  pass_sequentialize (pass_remove_special_ops fnlet)


(* Actual CIL translation *)
open Cil
open CilTools


let deffile = { fileName = "fnexpr_to_cil_translation";
                globals = [];
                globinit = None;
                globinitcalled = false;}

let defloc = { line = 0; file = "fnexpr_to_cil_translation" ; byte = 0; }


let conversion_error () = failwith "Failed to convert FnExpr to Cil expression"

let makeFunCall x f args = Call (Some (Var x, NoOffset), f, args, defloc)

let expr_to_cil fd temps e =
  let rec lval_or_error e =
    (match (fnexpr_to_exp e) with
     | Lval (lhost, loffset) -> (lhost, loffset)
     | _ -> conversion_error ())

  and fnexpr_to_exp e =
    let syt = type_of e in
    let t =
      match ciltyp_of_symb_type (type_of e) with
      | Some ot -> ot
      | None ->
        eprintf "Unknown type in expr to cil conversion :b %a" pp_typ syt;
        failwith "Type error."
    in
    match e with
    | FnVar v -> Lval (fnvar_to_lval v)
    | FnConst c -> constant c
    | FnAddrof e -> AddrOf (lval_or_error e)
    | FnAddrofLabel sref -> AddrOfLabel sref
    (* SizeOf operations *)
    | FnSizeof t -> SizeOf (check_option (ciltyp_of_symb_type t))
    | FnSizeofE e -> SizeOfE (fnexpr_to_exp e)
    | FnSizeofStr s -> SizeOfStr s
    (* Cast operations *)
    | FnCastE (t, e) ->
      let ct = check_option (ciltyp_of_symb_type t) in
      CastE (ct, fnexpr_to_exp e)
    (* ALignment operations *)
    | FnAlignof t -> AlignOf (check_option (ciltyp_of_symb_type t))
    | FnAlignofE e -> AlignOfE (fnexpr_to_exp e)
    (* Start of *)
    | FnStartOf e -> StartOf (lval_or_error e)

    | FnCond (c, e1, e2) ->
      Question (fnexpr_to_exp c, fnexpr_to_exp e1, fnexpr_to_exp e2, t)

    | FnApp (st, fo, args) ->
      let new_temp = makeTempVar fd t in
      fd.slocals <- fd.slocals@[new_temp];
      (match fo with
       | Some vi ->
         let vi =  makeVarinfo false vi.vname
             (check_option (ciltyp_of_symb_type vi.vtype)) in
         temps :=
           !temps@[(makeFunCall
                      new_temp
                      (Lval (Var vi, NoOffset))
                      (List.map fnexpr_to_exp args))];
         Lval (Var new_temp, NoOffset)
       (** Should not happen ! *)
       | None ->
         eprintf "Creating an empty temporary with no value.\
                  A function application with no function name was encoutered.";
         Lval (Var new_temp, NoOffset))

    (* Binary operations *)
    | FnBinop (op, e1, e2) ->
      begin
        match op with
        | Neq ->
          UnOp (BNot, fnexpr_to_exp (FnBinop (Eq, e1, e2)), t)
        | _ ->
          begin
            match (cil_binop_of_symb_binop op) with
            | Some bop, _ ->
              BinOp (bop, fnexpr_to_exp e1, fnexpr_to_exp e2, t)
            | None, Some func ->
              let new_temp = makeTempVar fd t in
              fd.slocals <- fd.slocals@[new_temp];
              temps :=
                !temps@[(makeFunCall
                           new_temp func [fnexpr_to_exp e1; fnexpr_to_exp e2])];
              (** Replace by the temp variable, once the corresponding function
                  call to place before is "remembered" *)
              Lval (Var new_temp, NoOffset)

            | _, _ -> failwith "Unreachable match case"
          end
      end

    | FnUnop (op, e1) ->
      begin
        match op with
        | Add1->
          fnexpr_to_exp (FnBinop (Plus, e1, FnConst (CInt 1)))
        | Sub1 ->
          fnexpr_to_exp (FnBinop (Minus, e1, FnConst (CInt 1)))
        | _ ->
          begin
            match (cil_unop_of_symb_unop op) with
            | Some uop, _ ->
              UnOp (uop, fnexpr_to_exp e1, t)
            | None, Some func ->
              let new_temp = makeTempVar fd t in
              fd.slocals <- fd.slocals@[new_temp];
              temps :=
                !temps@[(makeFunCall new_temp func [fnexpr_to_exp e1])];
              Lval (Var new_temp, NoOffset)

            | _, _ -> failwith "Unreachable match case."
          end
      end

    | FnHoleL _ | FnHoleR _ -> failwith "Holes cannot be converted"
    | FnFun _ | FnRec _ -> failwith "Control flow not supported"
    | FnRecord _  -> failhere __FILE__ "fnvar_to_lval" "Tuple and vectors not yet implemented."
    | FnRecordMember _ -> failhere __FILE__ "exp_to_cil" "Record member not supported."
    | FnArraySet _ -> failhere __FILE__ "exp_to_cil" "Array set operation not supported."
    | FnLetExpr _ -> failhere __FILE__ "exp_to_cil" "Let expr not supported."
    | FnLetIn  _ -> failhere __FILE__ "exp_to_cil" "Let in not supported."
    | FnVector _ -> failhere __FILE__ "exp_to_cil" "Vector literal not supported."
    | FnChoice _ -> failhere __FILE__ "exp_to_cil" "Choice leaking to cil translation."

  and fnvar_to_lval v =
    match v with
    | FnVariable vi ->
      let v = cil_varinfo vi in
      Var v , NoOffset
    | FnArray (v, e) ->
      let lh, offset = fnvar_to_lval v in
      lh , Index (fnexpr_to_exp e, offset)



  and cil_binop_of_symb_binop binop =
    let maybe_binop =
      match binop with
      | And -> Some BAnd
      | Or -> Some BOr
      | Plus -> Some PlusA
      | Minus -> Some MinusA
      | Times -> Some Mult
      | Div -> Some Div
      | Eq -> Some Eq | Lt -> Some Lt | Le -> Some Le | Gt -> Some Gt
      | Ge -> Some Ge
      | ShiftL -> Some Shiftlt
      | ShiftR -> Some Shiftrt
      | _ -> None
    in
    match maybe_binop with
    | Some binop -> Some binop, None
    | None ->
      None,
      Some (Lval (Var (let funname =
                         (match binop with
                          | Min -> "MIN"
                          | Max -> "MAX"
                          | _ -> "" )
                       in
                       makeVarinfo false funname (TInt (IInt, []))), NoOffset))


  and cil_unop_of_symb_unop op =
    let maybe_op =
      match op with
      | Neg -> Some Neg
      | Not -> Some BNot
      | _ -> None
    in
    match maybe_op with
    | Some op -> Some op, None
    | None ->
      None,
      Some (Lval (Var (let fname, t =
                         match op with
                         | Floor -> "floor",
                                    CilTools.simple_fun_type INT [FLOAT]
                         | Round -> "round",
                                    CilTools.simple_fun_type INT [FLOAT]
                         | Truncate -> "truncate",
                                       CilTools.simple_fun_type INT [FLOAT]
                         | Abs -> "abs",
                                  CilTools.simple_fun_type INT [INT]
                         | Ceiling -> "ceil",
                                      CilTools.simple_fun_type INT [FLOAT]
                         | Sgn -> "signof",
                                  CilTools.simple_fun_type FLOAT [FLOAT]
                         | _ -> "", CilTools.simple_type BOOL
                       in
                       makeVarinfo false fname t),
                  NoOffset))
  and constant c =
    match c with
    | CInt i -> Const (CInt64 (Int64.of_int i, IInt, None))
    | CBool t -> Const (if t then CInt64 (1L, IBool, None)
                        else CInt64 (0L, IBool, None))
    | CInt64 i -> Const (CInt64 (i, IInt, None))
    | CChar c -> Const (CChr c)
    | CString s -> Const (CStr s)
    | CReal r -> Const (CReal (r, FFloat, None))

    | CNil -> failwith "Cannot convert Nil constant to Cil.\
                        There must be a mistake ..."
    | CBox _ -> failwith "Not yet implemented (CBox)"
    | CUnop (op, c) ->
      fnexpr_to_exp (FnUnop (op, FnConst c))

    | CBinop (op, c1, c2) ->
      fnexpr_to_exp (FnBinop (op, FnConst c1, FnConst c2))

    | _ -> failwith "Unsupported constants."
  in
  fnexpr_to_exp e

let rec fnvar_to_cil fd tmps v =
  match v with
  | FnVariable v ->
    let v = cil_varinfo v in
    (Var v , NoOffset)
  | FnArray (v, e) ->
    let lh, offset = fnvar_to_cil fd tmps v in
    lh , Index (expr_to_cil fd tmps e, offset)


(** Let bindings to imperative code. *)
let sort_nb_used_vars (v1, e1) (v2, e2) =
  let used1 = used_in_fnexpr e1 in
  let used2 = used_in_fnexpr e2 in
  let vi1 = check_option (vi_of v1) in
  let vi2 = check_option (vi_of v2) in
  match VarSet.mem vi1 used2, VarSet.mem vi2 used1 with
  | false, false ->
    if VarSet.cardinal used1 > VarSet.cardinal used2 then 1 else -1
  | true, false -> 1
  | false, true -> -1
  (* Case with a conflict ! Needs a temp variable. *)
  | true, true -> 1


let fnlet_to_stmts fd fnlet =
  let add_assignments =
    List.fold_left
      (fun blk (v, e) ->
         match e with
         | FnVar v' when v' = v -> blk
         | _ ->
           let tmp_asgn = ref [] in
           let new_e = expr_to_cil fd tmp_asgn e in
           let lval_v = fnvar_to_cil fd tmp_asgn v in
           (add_instr
              blk
              ((!tmp_asgn)@[Set (lval_v, new_e, defloc)])))
  in
  let rec translate_let fnlet instr_li_stmt =
    match fnlet with
    | FnLetIn (asgn_li, letin) ->
      let a_block =
        add_assignments instr_li_stmt
          (List.sort sort_nb_used_vars asgn_li)
      in
      translate_let letin a_block
    | FnLetExpr a_list ->
      add_assignments instr_li_stmt (List.sort sort_nb_used_vars a_list)

    | _ -> instr_li_stmt
  in
  let empty_statement = { labels = []; sid = new_sid ();
                          skind = Instr []; preds = []; succs = [] }
  in
  fd, translate_let fnlet empty_statement
