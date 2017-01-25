open Utils
open Format
open Findloops
open Ast

(**
   1 - Expressions & functions.
   2-  Symbolic types, operators, helper functions.
   3 - Recursors.
   4 - Scheme & sketch trasnformers.
   5 - Expression sets.
   6 - Index variables management.
   7 - Typing expressions.
   8 - Structs for problem info.
*)

let use_unsafe_operations = ref false


(** ------------------- 1 - EXPRESSIONS & FUNCTIONS---------------------------*)
(** Internal type for building sketches *)

type sklet =
  | SkLetExpr of (skLVar * skExpr) list
  (**  (let ([var expr]) let)*)
  | SkLetIn of (skLVar * skExpr) list * sklet

and skLVar =
  | SkVarinfo of Cil.varinfo
  (** Access to an array cell *)
  | SkArray of skLVar * skExpr
  (** Records : usefule to represent the state *)
  | SkTuple of VS.t

and skExpr =
  | SkVar of skLVar
  | SkConst of constants
  | SkFun of sklet
  | SkRec of  forIGU * sklet
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



(** ----------- 2 - SYMBOLIC TYPES & OPERATORS, HELPER FUNCTIONS -------------*)
(** Interface types with Rosette/Racket *)

and symbolic_type =
    | Bottom
  | Num
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

let symb_unop_of_cil =
  function
  | Cil.LNot -> Not, Bottom
  | Cil.BNot -> Not, Boolean
  | Cil.Neg -> Neg, Num

let symb_binop_of_cil =
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

(* number?, real?, integer?, zero?, positive?, negative?, even?, odd?, *)
(* inexact->exact, exact->inexact, quotient , sgn *)


(** Identity function *)
let identity_sk =
  SkLetExpr ([])


(** C Standard Library function names -> Rosette supported functions *)
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

let symb_binop_of_fname =
  function
  | "modf" | "modff" | "modfl" -> None (** TODO *)
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
(**
    Mathematical constants defined in GNU-GCC math.h.
   + other custom constants defined in the decl_header.c

   ****   ****   ****   ****   ****   ****   ****
    TODO : integrate log/ln/pow function, not in
    rosette/safe AFAIK.
*)
let c_constant  ccst =
  match ccst with
  | "true___0" -> Some (CBool true)
  | "false___0" -> Some (CBool false)
  | "_min_int" -> Some NInfnty
  | "_max_int_" -> Some Infnty
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

(**
    A function name not appearing in the cases above
    will be treated as an "uninterpreted function" by
    default.
    TODO :
    -> Unless it is a user-specified function that can
    be interpreted easily (ex : custom max)
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


let remove_interpreted_symbols (vars : VS.t) =
  VS.filter
    (fun v -> uninterpeted v.Cil.vname)
    vars

let is_exp_function ef =
  match ef with
  | Cil.Lval (Cil.Var vi, _) ->
    let fname = vi.Cil.vname in
    let ty = vi.Cil.vtype in
    uninterpeted fname, Some vi, ty

  | _ -> false,  None , Cil.typeOf ef

(**
   Generate a SkVar expression from a varinfo, with possible offsets
   for arrays. Checks first if the name of the variable is a predefined
   constant.
*)
let mkVar ?(offsets = []) vi =
  List.fold_left
    (fun sklvar offset -> SkArray (sklvar, offset))
    (SkVarinfo vi)
    offsets

let mkVarExpr ?(offsets = []) vi =
  match c_constant vi.Cil.vname with
  | Some c -> SkConst c
  | None -> SkVar (mkVar ~offsets:offsets vi)

let rs_prefix = (Conf.get_conf_string "rosette_join_right_state_prefix")

let is_right_state_varname s =
  let varname_parts = Str.split (Str.regexp "\.") s in
  let right_state_name = (Str.split (Str.regexp "\.") rs_prefix) >> 0 in
    match List.length varname_parts with
    | 2 -> varname_parts >> 1, (varname_parts >> 0) = right_state_name
    | 1 -> varname_parts >> 0, false
    | _ ->
      failwith (fprintf str_formatter
                  "Unexpected list length when splitting variable name %s \
                   over '.'" s; flush_str_formatter ())



let rec cmpVar sklvar1 sklvar2 =
  match sklvar1, sklvar2 with
  | SkVarinfo vi, SkVarinfo vi' -> compare vi.Cil.vid vi'.Cil.vid
  | SkArray (sklv1, _), SkArray (sklv2, _) ->
    cmpVar sklv1 sklv2
  | SkVarinfo _, SkTuple _ -> -1
  | SkTuple _ , _ -> 1
  | SkArray _ , _ -> 1
  | _ , SkArray _ -> -1


let rec vi_of sklv =
  match sklv with
  | SkVarinfo vi' -> Some vi'
  | SkArray (sklv', _) -> vi_of sklv'
  | SkTuple _ -> None

let is_vi sklv vi = maybe_apply_default (fun x -> vi = x) (vi_of sklv) false

let is_reserved_name s = not (uninterpeted s)

(** Remove interpreted symbols from a set of vars *)
let remove_reserved_vars vs =
  VS.filter
    (fun vi ->
       (if uninterpeted vi.Cil.vname then
          (if !debug then printf "@.Removing %s." vi.Cil.vname; true)
        else false)) vs


let mkOp ?(t = Unit) vi argl =
  let fname = vi.Cil.vname in
  match symb_unop_of_fname fname with
  | Some unop ->
    SkUnop (unop, List.hd argl)
  | None ->
    match symb_binop_of_fname fname with
    | Some binop ->
      SkBinop (binop, List.hd argl, List.nth argl 2)
    | None ->
      SkApp (t, Some vi, argl)

let rec symb_type_of_ciltyp =
  function
  | Cil.TInt (ik, _) ->
    begin
      match ik with
      | Cil.IBool -> Boolean
      | _ -> Integer
    end

  | Cil.TFloat _ -> Real

  | Cil.TArray (t, _, _) ->
    Vector (symb_type_of_ciltyp t, None)

  | Cil.TFun (t, arglisto, _, _) ->
    Procedure (symb_type_of_args arglisto, symb_type_of_ciltyp t)
  | Cil.TComp (ci, _) -> Unit
  | Cil.TVoid _ -> Unit
  | Cil.TPtr (t, _) ->
    Vector (symb_type_of_ciltyp t, None)
  | Cil.TNamed (ti, _) ->
    symb_type_of_ciltyp ti.Cil.ttype
  | Cil.TEnum _ | Cil.TBuiltin_va_list _ -> failwith "Not implemented"

and symb_type_of_args argslisto =
  try
    let argslist = check_option argslisto in
    let symb_types_list =
      List.map
        (fun (s, t, atr) -> symb_type_of_ciltyp t)
        argslist
    in
    match symb_types_list with
    | [] -> Unit
    | [st] -> st
    | _ -> Tuple symb_types_list
  with Failure s -> Unit

let rec symb_type_of_cilconst c =
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


(** ---------------------------- 3 - RECURSORS -------------------------------*)


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
    (case : skExpr -> bool)
    (case_handler : skExpr -> 'a)
    (const_handler: constants -> 'a)
    (var_handler : skLVar -> 'a)
    (expre : skExpr) : 'a =

  let rec recurse_aux =
    function
    | e when case e -> case_handler e
    | SkVar v -> var_handler v
    | SkConst c -> const_handler c

    | SkBinop (_, e1, e2) ->
      join (recurse_aux e1) (recurse_aux e2)

    | SkCastE (_, e)
    | SkAlignofE e
    | SkAddrof e
    | SkSizeofE e | SkStartOf e
    | SkUnop (_, e) -> recurse_aux e

    | SkQuestion (c, e1, e2) ->
      join (join (recurse_aux c) (recurse_aux e1)) (recurse_aux e2)

    | SkApp (_, _, el) ->
      List.fold_left (fun a e -> join a (recurse_aux e)) init el

    | SkFun letin
    | SkRec (_, letin) -> recurse_letin letin

    | SkCond (c, l1, l2) ->
      join (recurse_aux c) (join (recurse_letin l1) (recurse_letin l2))

    | _ -> init

  and recurse_letin =
    function
    | SkLetExpr velist ->
      List.fold_left (fun acc (v, e) -> join acc (recurse_aux e))
        init velist

    | SkLetIn (velist, letin) ->
      let in_letin = recurse_letin letin in
      List.fold_left
        (fun acc (v, e) -> join acc (recurse_aux e)) in_letin velist
  in
  recurse_aux expre

(** Another recursion helper : a syntax tree tranformer *)
let transform_expr
    (case : skExpr -> bool)
    (case_handler : (skExpr -> skExpr) -> skExpr -> skExpr)
    (const_handler: constants -> constants)
    (var_handler : skLVar -> skLVar)
    (expre : skExpr) : 'a =

  let rec recurse_aux =
    function
    | e when case e ->
      case_handler recurse_aux e

    | SkVar v -> SkVar (var_handler v)
    | SkConst c -> SkConst (const_handler c)

    | SkBinop (op, e1, e2) ->
      SkBinop (op, (recurse_aux e1), (recurse_aux e2))

    | SkCastE (t, e) -> SkCastE (t, recurse_aux e)
    | SkAlignofE e -> SkAlignofE (recurse_aux e)
    | SkAddrof e -> SkAddrof (recurse_aux e)
    | SkSizeofE e -> SkSizeofE (recurse_aux e)
    | SkStartOf e -> SkStartOf (recurse_aux e)
    | SkUnop (op, e) -> SkUnop (op, recurse_aux e)

    | SkQuestion (c, e1, e2) ->
      SkQuestion (recurse_aux c, recurse_aux e1, recurse_aux e2)

    | SkApp (a, b, el) ->
      SkApp (a, b, List.map (fun e -> recurse_aux e) el)

    | SkFun letin -> SkFun (recurse_letin letin)
    | SkRec (igu, letin) -> SkRec (igu, recurse_letin letin)

    | SkCond (c, l1, l2) ->
      SkCond (recurse_aux c, recurse_letin l1, recurse_letin l2)

    | e -> e

  and recurse_letin =
    function
    | SkLetExpr velist ->
      SkLetExpr (List.map (fun (v, e) -> (v, recurse_aux e)) velist)

    | SkLetIn (velist, letin) ->
      let in_letin = recurse_letin letin in
      SkLetIn (List.map (fun (v, e) -> (v, (recurse_aux e))) velist, in_letin)
  in
  recurse_aux expre

(** Transformation with extra boolean argument *)
let transform_expr_flag
    (top : bool)
    (case : bool -> skExpr -> bool)
    (case_handler : bool-> (bool -> skExpr -> skExpr) -> skExpr -> skExpr)
    (const_handler: bool -> constants -> constants)
    (var_handler : bool ->skLVar -> skLVar)
    (expre : skExpr) : 'a =

  let rec recurse_aux flag =
    function
    | e when case flag e ->
      case_handler flag recurse_aux e

    | SkVar v -> SkVar(var_handler flag v)
    | SkConst c -> SkConst (const_handler flag c)

    | SkBinop (op, e1, e2) ->
      SkBinop (op, (recurse_aux flag e1), (recurse_aux flag e2))

    | SkCastE (t, e) -> SkCastE (t, recurse_aux flag e)
    | SkAlignofE e -> SkAlignofE (recurse_aux flag e)
    | SkAddrof e -> SkAddrof (recurse_aux flag e)
    | SkSizeofE e -> SkSizeofE (recurse_aux flag e)
    | SkStartOf e -> SkStartOf (recurse_aux flag e)
    | SkUnop (op, e) -> SkUnop (op, recurse_aux flag e)

    | SkQuestion (c, e1, e2) ->
      SkQuestion (recurse_aux flag c, recurse_aux flag e1, recurse_aux flag e2)

    | SkApp (a, b, el) ->
      SkApp (a, b, List.map (fun e -> recurse_aux flag e) el)

    | SkFun letin -> SkFun (recurse_letin flag letin)
    | SkRec (igu, letin) -> SkRec (igu, recurse_letin flag letin)

    | SkCond (c, l1, l2) ->
      SkCond (recurse_aux flag c, recurse_letin flag l1, recurse_letin flag l2)

    | e -> e

  and recurse_letin flag =
    function
    | SkLetExpr velist ->
      SkLetExpr (List.map (fun (v, e) -> (v, recurse_aux flag e)) velist)

    | SkLetIn (velist, letin) ->
      let in_letin = recurse_letin flag letin in
      SkLetIn (List.map (fun (v, e) ->
          (v, (recurse_aux flag e))) velist, in_letin)
  in
  recurse_aux top expre

(** An application of a function transformer : replace
    expression to_replace by expression by.
*)
let rec replace_expression ?(in_subscripts = false)
    ~to_replace:tr ~by:b ~ine:exp=
  let case e = (e = tr) in
  let case_handler rfunc e = b in
  let const_handler c = c in
  let var_handler v =
    if in_subscripts then
      match v with
      | SkArray (v, e) ->
        SkArray (v,
                 replace_expression ~in_subscripts:true ~to_replace:tr ~by:b
                   ~ine:e)
      | _ -> v
    else
      v
  in
  transform_expr case case_handler const_handler var_handler exp

let rec sk_uses vs expr =
  let join a b = a || b in
  let case e = false in
  let case_handler e = false in
  let const_handler c = false in
  let var_handler v =
    try VS.mem (check_option (vi_of v)) vs with Not_found -> false
  in rec_expr join false case case_handler const_handler var_handler expr

(** Compose a function by adding new assignments *)
let rec remove_id_binding func =
  let aux_rem_from_list el =
    List.filter
      (fun (v,e) -> not (e = SkVar v)) el
  in
  match func with
  | SkLetExpr el -> SkLetExpr (aux_rem_from_list el)
  | SkLetIn (el, c) -> SkLetIn (aux_rem_from_list el, remove_id_binding c)

let rec compose func1 func2 =
  match func1 with
  | SkLetExpr el -> SkLetIn (el, func2)
  | SkLetIn (el, c) -> SkLetIn (el, compose c func2)

let compose_head assignments func =
  match assignments with
  | [] -> func
  | _ -> SkLetIn (assignments, func)

let rec compose_tail assignments func =
  match assignments with
  | [] -> func
  | _ ->
    match func with
    | SkLetExpr el ->
      SkLetIn (el, SkLetExpr assignments)
    | SkLetIn (el, l) -> SkLetIn (el, compose_tail assignments l)

let complete_with_state stv el =
  (* Map the final expressions *)
  let emap =
    List.fold_left
      (fun map (v,e) ->
         let vi = check_option (vi_of v) in
         IM.add vi.Cil.vid (v, e) map)
      IM.empty el
  in
  let map' =
    VS.fold
      (fun vi map ->
         if IM.mem vi.Cil.vid map then map
         else IM.add vi.Cil.vid (mkVar vi, mkVarExpr vi) map)
      stv emap
  in
  let _, velist = ListTools.unpair (IM.bindings map') in
  velist

let rec complete_final_state stv func =
  match func with
  | SkLetExpr el -> SkLetExpr (complete_with_state stv el)
  | SkLetIn (el, l) -> SkLetIn (el, complete_final_state stv l)


let used_in_skexpr =
  let join = VS.union in
  let init = VS.empty in
  let case e = false in
  let case_h e = VS.empty in
  let var_handler v =
    let vi = vi_of v in
    match vi with | Some vi -> VS.singleton vi | _ -> VS.empty
  in
  let const_handler c= VS.empty in
  rec_expr join init case case_h const_handler var_handler


let rec used_in_sklet =
  function
  | SkLetIn (ve_list, letin) ->
    let bs1, us1 = (used_in_sklet letin) in
    let bs2, us2 = (used_in_assignments ve_list) in
    (VS.union bs1 bs2, VS.union us1 us2)
  | SkLetExpr ve_list ->
    used_in_assignments ve_list

and used_in_assignments ve_list =
  List.fold_left
    (fun (bind_set, use_set) (v, e) ->
       (VS.union bind_set
          (match vi_of v with
           | Some vi -> VS.singleton vi
           | None -> VS.empty),
        VS.union use_set (used_in_skexpr e)))
    (VS.empty, VS.empty) ve_list


(** ------------------------ 4 - SCHEME <-> SKETCH -------------------------- *)
(** Translate basic scheme to the Sketch expressions
    @param env a mapping from variable ids to varinfos.
*)

let errmsg_unexpected_sklet unex_let =
    (fprintf str_formatter "Expected a translated expression,\
                            received for tranlsation @; %a @."
       Ast.pp_expr unex_let;
     flush_str_formatter ())

let errmsg_unexpected_expr ex_type unex_expr =
  (fprintf str_formatter "Expected a %s ,\
                            received for tranlsation @; %a @."
     ex_type Ast.pp_expr unex_expr;
     flush_str_formatter ())


type join_translation_info = {
  mutable initial_vars : VS.t;
  mutable initial_state_vars : VS.t;
  mutable used_vars : Cil.varinfo SH.t;
  mutable used_state_vars : VS.t;
  initial_state_right : Cil.varinfo IH.t;
  initial_state_left: Cil.varinfo IH.t;
}

let get_binop_of_scm (op : Ast.op) =
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
  | _ -> failwith "Scheme binary operator not supported"

let get_unop_of_scm  (op : Ast.op)=
  match op with
  | Not -> Not
  | _ -> failwith "Scheme unary operator not supported"

let co = check_option

let join_info =
  {
    initial_vars = VS.empty;
    initial_state_vars = VS.empty;
    used_vars = SH.create 10;
    used_state_vars = VS.empty;
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
  let pure_varname, is_class_member = is_right_state_varname s in
  let varinfo =
    try
    SH.find join_info.used_vars pure_varname
  with Not_found ->
    begin
      let newly_used_vi =
        try
          VSOps.find_by_name pure_varname join_info.initial_vars
        with
        | Not_found ->
          Cil.makeVarinfo false pure_varname (Cil.TVoid [])
      in
      SH.add join_info.used_vars pure_varname newly_used_vi;
    newly_used_vi
    end
  in
  {varinfo with Cil.vname = s}




let rec scm_to_sk scm =
  try
    match scm with
    | Int_e i -> None, Some (SkConst (CInt i))
    | Str_e s -> None, Some (SkConst (CString s))
    | Bool_e b -> None, Some (SkConst (CBool b))
    | Id_e id ->
      (let vi = scm_register id in
      None, Some (SkVar (SkVarinfo vi)))
    | Nil_e -> None, Some (SkConst (CNil))

    | Binop_e (op, e1, e2) ->
      let _, e1' = scm_to_sk  e1 in
      let _, e2' = scm_to_sk  e2 in
      None, Some (SkBinop (get_binop_of_scm op, co e1', co e2'))

    | Unop_e (op, e) ->
      let _, e' = scm_to_sk  e in
      None, Some (SkUnop (get_unop_of_scm op, co e'))

    | Cons_e (x, y)-> failwith "Cons not supported"

    | Let_e (bindings, e2)
    | Letrec_e (bindings, e2) ->
      let bds = List.map
          (fun (ids, e) ->
             let _, exp = scm_to_sk e in
             let vi = scm_register ids in
             (SkVarinfo vi), co exp)
          bindings
      in
      let sk_let, _ = scm_to_sk  e2 in
      Some (SkLetIn (bds, co sk_let)), None

    | If_e (c, e1, e2) ->
      let _, cond = scm_to_sk  c in
      let le1, ex1 = scm_to_sk  e1 in
      let le2, ex2 = scm_to_sk  e2 in
      begin
        if is_some ex1 && is_some ex2 then
          None, Some (SkQuestion (co cond, co ex1, co ex2))
        else
          begin
            try
              None, Some (SkCond (co cond, co le1, co le2))
            with Failure s ->
              failwith (s^"\nUnexpected form in conditional.")
          end
      end
    | Apply_e (e, arglist) ->
      (match e with
       | Id_e s ->
         (match s with
          | "vector-ref" ->
            (None, Some (SkVar (to_array_var arglist)))
          | a when a = (Conf.get_conf_string "rosette_struct_name")  ->
            (Some (rosette_state_struct_to_sklet arglist), None)
          | _ ->
            (None, Some (to_fun_app e arglist)))
       | _ ->
      failwith "TODO")


    | Fun_e _ | Def_e _ | Defrec_e _ |Delayed_e _ | Forced_e _ ->
      failwith "Not supported"

  with Not_found ->
    failwith "Variable name not found in current environment."

(** Structure translation is parameterized by the current information
    loaded in the join_info. The order had been created using the order in
    the set of staate variables so we use the same order to re-build the
    expressions.
    Additionally we remove identity bindings.
*)
and rosette_state_struct_to_sklet scm_expr_list =
  let stv_vars_list = VSOps.varlist join_info.initial_state_vars in
  let sk_expr_list = to_expression_list scm_expr_list in
  try
    SkLetExpr (ListTools.pair (List.map (fun vi -> SkVarinfo vi) stv_vars_list)
                 sk_expr_list)
  with Invalid_argument s ->
    eprintf "FAILURE :@\n\
             Failed to translate state in list of bindings, got %i state \
             variables and state was %i long.@\n\
             ---> Did you initialize the join_info before using scm_to_sk ?"
      (VS.cardinal join_info.initial_state_vars)
      (List.length sk_expr_list);
    failwith "Failure in rosette_state_struct_to_sklet."

and to_expression_list scm_expr_list =
  List.map
    (fun scm_expr ->
       match scm_to_sk scm_expr with
       | None, Some sk_expr -> sk_expr
       | Some sklet, None->
           raise (Failure (errmsg_unexpected_sklet scm_expr))
       | _ ->
         failwith "Unexpected case.") scm_expr_list

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
  SkApp (Bottom, Some fun_vi, args)



let translate_join i_all_vs i_st_vs = ();;


(** ------------------------ 5 -  EXPRESSION SET ----------------------------*)

module ES = Set.Make (
  struct
    let compare = Pervasives.compare
    type t = skExpr
  end)


(** Context for expression analysis *)
type context = {
  state_vars : VS.t;
  index_vars : VS.t;
  used_vars : VS.t;
  all_vars : VS.t;
  costly_exprs : ES.t
}

let mk_ctx vs stv = {
  state_vars = stv;
  index_vars = VS.empty;
  used_vars = VS.diff stv vs;
  all_vars = vs;
  costly_exprs = ES.empty
}

let ctx_update_vsets ctx vs =
  let new_allvs = VS.union ctx.all_vars vs in
  let new_usedvs = VS.union ctx.used_vars vs in
  let new_stvs = VS.union ctx.state_vars vs in
  { ctx with
    state_vars = new_stvs;
    used_vars = new_usedvs;
    all_vars =  new_allvs }

let ctx_add_cexp ctx cexp =
  {ctx with costly_exprs = cexp}


(** ------------------- 6 - INDEX VARIABLES MANAGEMENT -----------------------*)
(** Create and manage variables for index boundaries *)

let start_iname = Conf.get_conf_string "rosette_index_suffix_start"
let end_iname = Conf.get_conf_string "rosette_index_suffix_end"

let index_to_boundary : (Cil.varinfo * Cil.varinfo) IH.t = IH.create 10


let create_boundary_variables index_set =
  VS.iter
    (fun index_vi ->
       let starti =
         Cil.makeVarinfo false (index_vi.Cil.vname^start_iname)
           index_vi.Cil.vtype
       in
       let endi =
         Cil.makeVarinfo false (index_vi.Cil.vname^end_iname)
           index_vi.Cil.vtype
       in
       IH.add index_to_boundary index_vi.Cil.vid (starti, endi))
    index_set

let left_index_vi vi =
  if IH.length index_to_boundary = 0 then failwith "Empty index!" else ();
  let l, _ = IH.find index_to_boundary vi.Cil.vid in l


let right_index_vi vi =
  if IH.length index_to_boundary = 0 then failwith "Empty index!" else ();
  let _, r = IH.find index_to_boundary vi.Cil.vid in r


(* ------------------------ 7- TYPING EXPRESSIONS ----------------------------*)

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
  | Tuple tl ->
    Format.pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
      pp_typ fmt tl
  | Function (argt, rett) ->
    fpf fmt "%a -> %a" pp_typ argt pp_typ rett
  | Pair t -> fpf fmt "%a pair" pp_typ t
  | List (t, _) -> fpf fmt "%a list" pp_typ t
  | Struct t -> fpf fmt "%a struct" pp_typ t
  | Bitvector i -> fpf fmt "bitvector[%i]" i
  | Box t -> fpf fmt "%a box" pp_typ t
  | Procedure (tin, tout) -> fpf fmt "(%a %a proc)" pp_typ tin pp_typ tout

let rec is_subtype t tmax =
  match t, tmax with
  | t, tmax when t = tmax -> true
  | Integer, Real -> true
  | Num, Real | Real, Num -> true
  | Vector (t1', _), Vector(t2', _) -> is_subtype t1' t2'
  | _, _ ->
    failwith (Format.fprintf Format.str_formatter
                "Cannot join these types %a %a" pp_typ t pp_typ tmax;
              Format.flush_str_formatter () )

let rec res_type t =
  match t with
  | Function (t, t') -> t'
  | _ -> t

let rec join_types t1 t2 =
  match t1, t2 with
  | t1, t2 when t1 = t2 -> t1
  | Integer, Boolean -> Boolean
  | Integer, Real | Real, Integer
  | Num, Real | Real, Num -> Real
  | Integer, Num | Num, Integer -> Num
  | Vector (t1', _), Vector(t2', _) -> join_types t1' t2'
  | _, _ ->
    failwith (Format.fprintf Format.str_formatter
                "Cannot join these types %a %a" pp_typ t1 pp_typ t2;
              Format.flush_str_formatter () )


let type_of_unop t =
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


let type_of_binop t1 t2 =
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
  | CReal _ -> Real
  | CInt _ | CInt64 _ -> Integer
  | CBox b -> Box (symb_type_of_cilconst b)
  | CUnop (op, c) -> type_of (SkUnop (op, SkConst c))
  | CBinop (op, c, c') -> type_of (SkBinop (op, SkConst c, SkConst c'))
  | Pi | SqrtPi | Sqrt2 | E | Ln2 | Ln10 -> Real
  | CUnsafeBinop (op, c, c') -> join_types (type_of_const c) (type_of_const c')
  | CUnsafeUnop (op, c) -> (type_of_const c)
  | Infnty | NInfnty -> Num

and type_of_var v =
  match v with
  | SkVarinfo vi -> symb_type_of_ciltyp vi.Cil.vtype
  | SkArray (v, e) ->
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
  | SkTuple vs ->
    let tl =
      VS.fold (fun vi tl -> tl@[symb_type_of_ciltyp vi.Cil.vtype]) vs []
    in
    Tuple tl



and type_of expr =
  match expr with
  | SkVar v -> type_of_var v
  | SkConst c -> type_of_const c
  | SkAddrofLabel _ | SkStartOf _
  | SkSizeof _ | SkSizeofE _ | SkSizeofStr _
  | SkAlignof _ | SkAlignofE _  | SkAddrof _ -> Integer
  | SkCastE (t, e) -> t
  | SkUnop (unop, e) ->
    (match type_of_unop (type_of e) unop with
     | Some x -> x | None -> failwith "Could not find type of expressions.")

  | SkBinop (binop, e1, e2) ->
    (match type_of_binop (type_of e1) (type_of e2) binop with
     | Some x -> x | None -> failwith "Could not find type of expressions.")

  | SkQuestion (c, e1, e2) -> join_types (type_of e1) (type_of e2)

  | SkApp (t, _, _) | SkHoleL (_, t) | SkHoleR t -> t

  | _ -> failwith "Typing subfunctions not yet implemented"



(* ------------------------ 7- STRUCT UTILS ----------------------------*)

type sigu = VS.t * (sklet * skExpr * sklet)

type sketch_rep =
  {
    id : int;
    host_function : Cil.fundec;
    loop_name : string;
    ro_vars_ids : int list;
    scontext : context;
    loop_body : sklet;
    join_body : sklet;
    join_solution : sklet;
    init_values : Ast.expr IM.t;
    sketch_igu : sigu;
    reaching_consts : skExpr IM.t
  }

let get_index_init sktch =
  let idx, (i, g, u) = sktch.sketch_igu in i

let get_index_update sktch =
  let idx, (i, g, u) = sktch.sketch_igu in u

let get_index_varset sktch =
  let idx, (i, g, u) = sktch.sketch_igu in idx

let get_index_guard sktch =
  let idx, (i, g, u) = sktch.sketch_igu in g


(* ------------------------ 7- CONVERSION TO CIL  ----------------------------*)

(** Includes passes to transform the code into an appropriate form *)

let rec pass_remove_special_ops =
  let remove_in_exprs =
    transform_expr
      (fun e -> match e with SkBinop _ -> true
                           | SkApp _ -> true
                           | _ -> false)
      (fun rfun e ->
         match e with
         | SkBinop (op, e1, e2) ->
           let e1' = rfun e1 in let e2' = rfun e2 in
           (match op with
            | Max ->
              SkQuestion (SkBinop(Gt, e1', e2'), e1', e2')

            | Min ->
              SkQuestion (SkBinop(Lt, e1', e2'), e1', e2')

            | Nand ->
              SkUnop (Not, SkBinop (And, e1', e2'))

            | Neq ->
              SkUnop (Not, SkBinop (Eq, e1, e2))

            | _ -> SkBinop (op, e1', e2'))

         | SkApp (st, vo, args) ->
           let args' = List.map rfun args in
           (if List.length args' >= 1 then
             (** Might be a binary operator ... *)
             (let e1 = args' >> 0 in
              match vo with
              | Some var ->
                (match String.lowercase var.Cil.vname with
                 | "max" ->
                   let e2 = args' >> 1 in
                   SkQuestion (SkBinop(Gt, e1, e2), e1, e2)
                 | "min" ->
                   let e2 = args' >> 1 in
                   SkQuestion (SkBinop(Lt, e1, e2), e1, e2)
                 | "add1" ->
                   SkBinop (Plus, e1, SkConst (CInt 1))
                 | "sub1" ->
                   SkBinop (Minus, e1, SkConst (CInt 1))
                 | _ -> SkApp(st, vo, args'))
              | None ->
                SkApp(st, vo, args'))
            else
              SkApp(st, vo, args'))

         | _ -> failwith "Bad rec case.") identity identity
  in
  function
  | SkLetIn (ve_list , letin) ->
    SkLetIn (List.map (fun (v, e) -> (v, remove_in_exprs e)) ve_list,
             pass_remove_special_ops letin)
  | SkLetExpr ve_list ->
    SkLetExpr (List.map (fun (v, e) -> (v, remove_in_exprs e)) ve_list)

let rec pass_sequentialize sklet =
  let rec reorganize ve_list let_queue =
    (** A variable should be only bound once in a binding group, therefore
        we can identify a binding only by the variables it binds to.
        This supports only scalar types ! n *)
    let modified_vars, vid_to_expr, depends_graph_unpure =
      List.fold_left
        (fun (modified_set, expr_map, dep_graph) (v, e) ->
           match e with
           | SkVar v -> modified_set, expr_map, dep_graph (* Identity binding *)
           | _ ->
             let vi =
               try check_option (vi_of v)
               with Failure s ->  failwith "Non-scalar type unsupported"
             in
             let expr_depends = used_in_skexpr e in
             (VS.add vi modified_set,
              IM.add vi.Cil.vid e expr_map,
              IM.add vi.Cil.vid expr_depends dep_graph))
        (VS.empty, IM.empty, IM.empty) ve_list
    in
    (* let depends_graph = IM.map (fun deps -> VS.inter deps modified_vars) *)
    (*     depends_graph_unpure *)
    (* in *)
    (** We need to implement here the algorithm described in :
        http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf *)
    let statement_order = VSOps.vids_of_vs modified_vars in
    List.fold_left
      (fun let_bindings vid ->
         SkLetIn ([SkVarinfo (VSOps.find_by_id vid modified_vars),
                   IM.find vid vid_to_expr], let_bindings))
           let_queue statement_order
    (** Analyze dependencies to produce bindings ordered such that
        the sequence of bindings yields to the same state as the functional
        version where all expressions are evaluated in one step. *)

  in

  let rec sequentialize_parallel_moves =
    function
    | SkLetIn (ve_list, letin) ->
      reorganize ve_list (pass_sequentialize letin)
    | SkLetExpr ve_list ->
      reorganize ve_list (SkLetExpr [])
  in
  let rec remove_empty_lets =
    function
    | SkLetIn (ve_list, letin) ->
      (match remove_empty_lets letin with
       | Some let_tail ->
         (match ve_list with
          | [] -> Some let_tail
          | _ -> Some (SkLetIn (ve_list, let_tail)))
       | None ->
         (match ve_list with
          | [] -> None
          | _ -> Some (SkLetExpr ve_list)))

    | SkLetExpr ve_list ->
      (match ve_list with
       | [] -> None
       | _ -> Some (SkLetExpr ve_list))
  in
  match remove_empty_lets (sequentialize_parallel_moves sklet) with
  | Some sklet -> sklet
  | None -> SkLetExpr []


let sk_for_c sklet =
  pass_sequentialize (pass_remove_special_ops sklet)


(* Actual CIL translation *)
open Cil
open CilTools


let deffile = { fileName = "skexpr_to_cil_translation";
                globals = [];
                globinit = None;
                globinitcalled = false;}

let defloc = { line = 0; file = "skexpr_to_cil_translation" ; byte = 0; }


let conversion_error () = failwith "Failed to convert SkExpr to Cil expression"

let makeFunCall x f args = Call (Some (Var x, NoOffset), f, args, defloc)

let expr_to_cil fd temps e =
  let rec lval_or_error e =
    (match (skexpr_to_exp e) with
     | Lval (lhost, loffset) -> (lhost, loffset)
     | _ -> conversion_error ())

  and skexpr_to_exp e =
    let syt = type_of e in
    let t =
      match ciltyp_of_symb_type (type_of e) with
      | Some ot -> ot
      | None ->
        eprintf "Unknown type in expr to cil conversion :b %a" pp_typ syt;
        failwith "Type error."
    in
    match e with
    | SkVar v -> Lval (skvar_to_lval v)
    | SkConst c -> constant c
    | SkAddrof e -> AddrOf (lval_or_error e)
    | SkAddrofLabel sref -> AddrOfLabel sref
    (* SizeOf operations *)
    | SkSizeof t -> SizeOf (check_option (ciltyp_of_symb_type t))
    | SkSizeofE e -> SizeOfE (skexpr_to_exp e)
    | SkSizeofStr s -> SizeOfStr s
    (* Cast operations *)
    | SkCastE (t, e) ->
      let ct = check_option (ciltyp_of_symb_type t) in
      CastE (ct, skexpr_to_exp e)
    (* ALignment operations *)
    | SkAlignof t -> AlignOf (check_option (ciltyp_of_symb_type t))
    | SkAlignofE e -> AlignOfE (skexpr_to_exp e)
    (* Start of *)
    | SkStartOf e -> StartOf (lval_or_error e)

    | SkQuestion (c, e1, e2) ->
      Question (skexpr_to_exp c, skexpr_to_exp e1, skexpr_to_exp e2, t)

    | SkApp (st, fo, args) ->
      let new_temp = makeTempVar fd t in
      fd.slocals <- fd.slocals@[new_temp];
      (match fo with
       | Some vi ->
         temps :=
           !temps@[(makeFunCall
                      new_temp
                      (Lval (Var vi, NoOffset))
                      (List.map skexpr_to_exp args))];
         Lval (Var new_temp, NoOffset)
       (** Should not happen ! *)
       | None ->
         eprintf "Creating an empty temporary with no value.\
                  A function application with no function name was encoutered.";
         Lval (Var new_temp, NoOffset))

    (* Binary operations *)
    | SkBinop (op, e1, e2) ->
      begin
        match op with
        | Neq ->
          UnOp (BNot, skexpr_to_exp (SkBinop (Eq, e1, e2)), t)
        | _ ->
          begin
            match (cil_binop_of_symb_binop op) with
            | Some bop, _ ->
              BinOp (bop, skexpr_to_exp e1, skexpr_to_exp e2, t)
            | None, Some func ->
              let new_temp = makeTempVar fd t in
              fd.slocals <- fd.slocals@[new_temp];
              temps :=
                !temps@[(makeFunCall
                           new_temp func [skexpr_to_exp e1; skexpr_to_exp e2])];
              (** Replace by the temp variable, once the corresponding function
                  call to place before is "remembered" *)
              Lval (Var new_temp, NoOffset)

            | _, _ -> failwith "Unreachable match case"
          end
      end

    | SkUnop (op, e1) ->
      begin
        match op with
        | Add1->
          skexpr_to_exp (SkBinop (Plus, e1, SkConst (CInt 1)))
        | Sub1 ->
          skexpr_to_exp (SkBinop (Minus, e1, SkConst (CInt 1)))
        | _ ->
          begin
            match (cil_unop_of_symb_unop op) with
            | Some uop, _ ->
              UnOp (uop, skexpr_to_exp e1, t)
            | None, Some func ->
              let new_temp = makeTempVar fd t in
              fd.slocals <- fd.slocals@[new_temp];
              temps :=
                !temps@[(makeFunCall new_temp func [skexpr_to_exp e1])];
              Lval (Var new_temp, NoOffset)

            | _, _ -> failwith "Unreachable match case."
          end
      end

    | SkHoleL _ | SkHoleR _ -> failwith "Holes cannot be converted"
    | SkFun _ | SkCond _ | SkRec _ -> failwith "Control flow not supported"

  and skvar_to_lval v =
    match v with
    | SkVarinfo v -> Var v , NoOffset
    | SkArray (v, e) ->
      let lh, offset = skvar_to_lval v in
      lh , Index (skexpr_to_exp e, offset)

    | SkTuple _ -> failwith "Tuple not yet implemented"


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
      skexpr_to_exp (SkUnop (op, SkConst c))

    | CBinop (op, c1, c2) ->
      skexpr_to_exp (SkBinop (op, SkConst c1, SkConst c2))

    | _ -> failwith "Unsupported constants."
  in
  skexpr_to_exp e

let rec skvar_to_cil fd tmps v =
  match v with
  | SkVarinfo v -> Var v , NoOffset
  | SkArray (v, e) ->
    let lh, offset = skvar_to_cil fd tmps v in
    lh , Index (expr_to_cil fd tmps e, offset)

  | SkTuple _ -> failwith "Tuple not yet implemented"


(** Let bindings to imperative code. *)
let sort_nb_used_vars (v1, e1) (v2, e2) =
  let used1 = used_in_skexpr e1 in
  let used2 = used_in_skexpr e2 in
  let vi1 = check_option (vi_of v1) in
  let vi2 = check_option (vi_of v2) in
  match VS.mem vi1 used2, VS.mem vi2 used1 with
  | false, false ->
    if VS.cardinal used1 > VS.cardinal used2 then 1 else -1
  | true, false -> 1
  | false, true -> -1
  (* Case with a conflict ! Needs a temp variable. *)
  | true, true -> 1


let sklet_to_stmts fd sklet =
  let add_assignments =
    List.fold_left
      (fun blk (v, e) ->
         match e with
         | SkVar v' when v' = v -> blk
         | _ ->
           let tmp_asgn = ref [] in
           let new_e = expr_to_cil fd tmp_asgn e in
           let lval_v = skvar_to_cil fd tmp_asgn v in
           (add_instr
              blk
              ((!tmp_asgn)@[Set (lval_v, new_e, defloc)])))
  in
  let rec translate_let sklet instr_li_stmt =
    match sklet with
    | SkLetIn (asgn_li, letin) ->
      let a_block =
        add_assignments instr_li_stmt
          (List.sort sort_nb_used_vars asgn_li)
      in
      translate_let letin a_block
    | SkLetExpr a_list ->
      add_assignments instr_li_stmt (List.sort sort_nb_used_vars a_list)
  in
  let empty_statement = { labels = []; sid = new_sid ();
                          skind = Instr []; preds = []; succs = [] }
  in
  fd, translate_let sklet empty_statement
