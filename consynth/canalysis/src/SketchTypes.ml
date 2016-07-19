open Utils
open Format
open Loops

let use_unsafe_operations = ref false


(** Internal type for building sketches *)

type sklet =
  | SkLetExpr of skExpr
  | SkLetIn of Cil.varinfo * skExpr * sklet

and skExpr =
  | SkVar of Cil.varinfo
  | SkArray of Cil.varinfo * (skExpr list)
  | SkCil of Cil.exp (** If expression doesn't contain state variables *)
  | SkBinop of Cil.binop * skExpr * skExpr
  | SkUnop of Cil.unop * skExpr
  | SkRec of  forIGU * skExpr
  | SkCond of skExpr * skExpr * skExpr
  | SkHoleL
  | SkHoleR
(** Simple translation of Cil exp needed to nest
    sub-expressions with state variables *)
  | SkConst of Cil.constant
  | SkLval of Cil.lval
  | SkSizeof of Cil.typ
  | SkSizeofE of skExpr
  | SkSizeofStr of string
  | SkAlignof of Cil.typ
  | SkAlignofE of skExpr
  | SkCastE of Cil.typ * skExpr
  | SkAddrof of Cil.lval
  | SkAddrofLabel of Cil.stmt ref
  | SkStartOf of Cil.lval

and skStmt =  Cil.varinfo * sklet

type sketch = VS.t * skStmt list

(** Structure types for Rosette sketches *)

type initialDefs =
  | Initials of (string * string) list [@@deriving_sexp]

(**
   The body of the join and the loop are Racket programs with
   holes insides.
*)
type racket_with_holes = string list [@@deriving_sexp]

(**
   A state is simply a list of variables that are modified
   during the loop.
*)
type state = string list [@@deriving_sexp]

(**
   We generate the body of the oririginal loop simply from
   the state variables and the list of function that are
   applied to each state variable.
*)
type bodyFunc =
  | DefineBody of state * racket_with_holes
  | DefineJoin of state * racket_with_holes
      [@@deriving_sexp]

(** Interface types with Rosette/Racket *)

type symbolicType =
  | Unit
  (** Base types : only booleans, integers and reals *)
  | Integer
  | Real
  | Boolean
  (** Type tuple *)
  | Tuple of symbolicType list
  (** Other lifted types *)
  | Bitvector of symbolicType * int
  (** A function in Rosette is an uniterpreted function *)
  | Function of symbolicType * symbolicType
  (** A procdedure is a reference to a procedure object *)
  | Procedure of symbolicType * symbolicType
  (** Pairs and lists *)
  | Pair of symbolicType
  | List of symbolicType * int option
  (** Vector and box *)
  | Vector of symbolicType * int option
  | Box of symbolicType
  (** User-defined structures *)
  | Struct of symbolicType

let ostring_of_baseSymbolicType =
  function
  | Integer -> Some "integer?"
  | Real -> Some "real?"
  | Boolean -> Some "boolean?"
  | _ -> None

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
    let argslist = checkOption argslisto in
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


(*
  Operators : Cil operators and C function names.
*)

type symb_unops =
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

type symb_binops =
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

(**
   Some racket function that are otherwise unsafe
   to use in Racket, but we might still need them.
*)
and symb_unsafe_unops =
  (** Trigonometric + hyp. functions *)
  | Sin | Cos | Tan | Sinh | Cosh | Tanh
  (** Anti functions *)
  | ASin | ACos | ATan | ASinh | ACosh | ATanh
  (** Other functions *)
  | Log | Log2 | Log10
  | Exp | Sqrt

and symb_unsafe_binops =
  | TODO

(** Some pre-defined constants existing in C99 *)
and constants =
  | Int of int
  | Real of float
  | Bool of bool
  | CUnop of symb_unops * constants
  | CBinop of symb_binops * constants * constants
  | CUnsafeUnop of symb_unsafe_unops * constants
  | CUnsafeBinop of symb_unsafe_binops * constants * constants
  | Pi | SqrtPi
  | Sqrt2
  | Ln2 | Ln10 | E

let symb_unop_of_cil =
  function
  | Cil.LNot | Cil.BNot -> Not
  | Cil.Neg -> Neg

let symb_binop_of_cil =
  function
  | Cil.IndexPI -> Plus
  | Cil.PlusA | Cil.PlusPI -> Plus
  | Cil.MinusA | Cil.MinusPI | Cil.MinusPP-> Minus
  | Cil.Mult -> Times
  | Cil.Div -> Div
  | Cil.Mod -> Mod
  | Cil.BXor -> Xor
  | Cil.BAnd | Cil.LAnd -> And
  | Cil.BOr | Cil.LOr -> Or
  | Cil.Lt -> Lt | Cil.Le -> Le | Cil.Gt -> Gt | Cil.Ge -> Ge
  | Cil.Eq -> Eq | Cil.Ne -> Neq
  | Cil.Shiftlt -> ShiftL | Cil.Shiftrt -> ShiftR

  (* number?, real?, integer?, zero?, positive?, negative?, even?, odd?, *)
  (* inexact->exact, exact->inexact, quotient , sgn *)

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
  | "fmax" | "fmaxf" | "fmaxl" -> Some Max
  | "fmin" | "fminf" | "fminl" -> Some Min
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
   ****   ****   ****   ****   ****   ****   ****
    TODO : integrate log/ln/pow function, not in
    rosette/safe AFAIK.
*)
let c_constant  ccst =
  match ccst with
  | "M_E" -> Some E
  | "M_LN2" -> Some Ln2
  | "M_LN10" -> Some Ln10
  | "M_PI" -> Some Pi
  | "M_PI_2" -> Some (CBinop (Div, Pi, (Int 2)))
  | "M_PI_4" -> Some (CBinop (Div, Pi, (Int 2)))
  | "M_1_PI" -> Some (CBinop (Div, (Real 1.0), Pi))
  | "M_2_PI" -> Some (CBinop (Div, (Real 2.0), Pi))
  | _ ->
     if !use_unsafe_operations then
       begin
         match ccst with
         | "M_SQRT2" -> Some Sqrt2
         | "M_SQRT1_2" ->
            Some (CBinop (Div, (Real 1.0), Sqrt2))
         | "M_2_SQRTPI" ->
            Some (CBinop (Div, (Real 2.0), SqrtPi))
         | "M_LOG10E" ->
            Some (CBinop (Div, (Real 1.0), Ln10))
         | "M_LOG2E" ->
            Some (CBinop (Div, (Real 1.0), Ln2))
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


(** Pretty-printing operators *)

let string_of_symb_unops =
  function
  | Not -> "Not" | Add1 -> "Add1" | Sub1 -> "Sub1"| Abs -> "Abs"
  | Floor -> "Floor" | Ceiling -> "Ceiling"  | Truncate -> "Truncate"
  | Round -> "Round" | Neg -> "Neg" | Sgn -> "Sgn"

let string_of_symb_binops =
  function
  | And -> "and"
  | Nand -> "nand" | Or -> "or" | Nor -> "nor" | Implies -> "implies"
  | Xor -> "xor"
  (** Integers and reals *)
  | Plus -> "+" | Minus -> "-" | Times -> "*" | Div -> "/"
  | Quot -> "quot" | Rem -> "rem" | Mod -> "mod"
  (** Max and min *)
  | Max -> "max" | Min -> "min"
  (** Comparison *)
  | Eq -> "=" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="
  | Neq -> "neq"
  (** Shift*)
  | ShiftL -> "shiftl" | ShiftR -> "shiftr"
  | Expt -> "expt"

(**
   Some racket function that are otherwise unsafe
   to use in Racket, but we might still need them.
*)
let string_of_unsafe_unops =
  function
  (** Trigonometric + hyp. functions *)
  | Sin -> "sin" | Cos -> "cos" | Tan -> "tan" | Sinh -> "sinh"
  | Cosh -> "cosh" | Tanh -> "tanh"
  (** Anti functions *)
  | ASin -> "asin" | ACos -> "acos" | ATan -> "atan" | ASinh -> "asinh"
  | ACosh -> "acosh" | ATanh
  (** Other functions *)
  | Log -> "log" | Log2 -> "log2" | Log10 -> "log10"
  | Exp -> "exp" | Sqrt -> "sqrt"

let rec pp_constants ppf =
  function
  | Int i -> fprintf ppf "%i" i
  | Real f -> fprintf ppf "%10.3f" f
  | Bool b -> fprintf ppf "%b" b
  | CUnop (op, c) ->
     fprintf ppf "(%s %a)" (string_of_symb_unops op) pp_constants c
  | CBinop (op, c1, c2) ->
     fprintf ppf "(%s %a %a)" (string_of_symb_binops op)
       pp_constants c1 pp_constants c2
  | CUnsafeUnop (unsop, c) -> fprintf ppf  ""
  | CUnsafeBinop (unsbop, c1, c2) -> fprintf ppf ""
  | Pi -> fprintf ppf "pi"
  | Sqrt2 -> fprintf ppf "(sqrt 2)"
  | Ln2 -> fprintf ppf "(log 2)"
  | Ln10 -> fprintf ppf "(log 10)"
  | SqrtPi -> fprintf ppf "(sqrt pi)"
  | E -> fprintf ppf "(exp 1)"
