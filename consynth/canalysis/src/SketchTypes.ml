open Cil
open Utils
open Loops

let use_unsafe_operations = ref false


(** Internal type for building sketches *)

type sklet =
  | SkLetExpr of skExpr
  | SkLetIn of varinfo * skExpr * sklet

and skExpr =
  | SkVar of varinfo
  | SkArray of varinfo * (skExpr list)
  | SkCil of exp (** If expression doesn't contain state variables *)
  | SkBinop of binop * skExpr * skExpr
  | SkUnop of unop * skExpr
  | SkRec of  forIGU * skExpr
  | SkCond of skExpr * skExpr * skExpr
  | SkHoleL
  | SkHoleR
(** Simple translation of Cil exp needed to nest
    sub-expressions with state variables *)
  | SkConst of constant
  | SkLval of lval
  | SkSizeof of typ
  | SkSizeofE of skExpr
  | SkSizeofStr of string
  | SkAlignof of typ
  | SkAlignofE of skExpr
  | SkCastE of typ * skExpr
  | SkAddrof of lval
  | SkAddrofLabel of stmt ref
  | SkStartOf of lval

and skStmt =  varinfo * sklet

type sketch = VS.t * skStmt list

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
  | TInt (ik, _) ->
     begin
       match ik with
       | IBool -> Boolean
       | _ -> Integer
     end

  | TFloat _ -> Real

  | TArray (t, _, _) ->
     Vector (symb_type_of_ciltyp t, None)

  | TFun (t, arglisto, _, _) ->
     Procedure (symb_type_of_args arglisto, symb_type_of_ciltyp t)
  | TComp (ci, _) -> Unit
  | TVoid _ -> Unit
  | TPtr (t, _) ->
     Vector (symb_type_of_ciltyp t, None)
  | TNamed (ti, _) ->
     symb_type_of_ciltyp ti.ttype
  | TEnum _ | TBuiltin_va_list _ -> failwith "Not implemented"

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

type symbUnops =
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

type symbBinops =
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
type symbUnsafeUnops =
  (** Trigonometric + hyp. functions *)
  | Sin | Cos | Tan | Sinh | Cosh | Tanh
  (** Anti functions *)
  | ASin | ACos | ATan | ASinh | ACosh | ATanh
  (** Other functions *)
  | Log | Log2 | Log10
  | Exp | Sqrt

type symbUnsafeBinops =
  | TODO

(** Some pre-defined constants existing in C99 *)
type constants =
  | Int of int
  | Real of float
  | Bool of bool
  | CUnop of symbUnops * constants
  | CBinop of symbBinops * constants * constants
  | CUnsafeUnop of symbUnsafeUnops * constants
  | CUnsafeBinop of symbUnsafeBinops * constants * constants
  | Pi | SqrtPi
  | Sqrt2
  | Ln2 | Ln10 | E

let symb_unop_of_cil =
  function
  | LNot | BNot -> Not
  | Neg -> Neg

let symb_binop_of_cil =
  function
  | IndexPI -> Plus
  | PlusA | PlusPI -> Plus
  | MinusA | MinusPI | MinusPP-> Minus
  | Mult -> Times
  | Div -> Div
  | Mod -> Mod
  | BXor -> Xor
  | BAnd | LAnd -> And
  | BOr | LOr -> Or
  | Lt -> Lt | Le -> Le | Gt -> Gt | Ge -> Ge
  | Eq -> Eq | Ne -> Neq
  | Shiftlt -> ShiftL | Shiftrt -> ShiftR

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
