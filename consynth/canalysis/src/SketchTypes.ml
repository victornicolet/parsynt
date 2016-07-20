open Utils
open Format
open Loops

let use_unsafe_operations = ref false


(** Internal type for building sketches *)

type sklet =
  | SkLetExpr of (skLVar * skExpr) list
  (**  (let ([var expr]) let)*)
  | SkLetIn of (skLVar * skExpr) list * sklet

and skLVar =
  | SkState
  | SkVarinfo of Cil.varinfo

and skExpr =
  | SkFun of sklet
  | SkRec of  forIGU * sklet
  | SkCond of skExpr * sklet * sklet

  | SkVar of Cil.varinfo
  | SkArray of Cil.varinfo * (skExpr list)
  | SkBinop of symb_binop * skExpr * skExpr
  | SkQuestion of skExpr * skExpr * skExpr
  | SkUnop of symb_unop * skExpr
  | SkHoleL
  | SkHoleR
(** Simple translation of Cil exp needed to nest
    sub-expressions with state variables *)
  | SkConst of constants
  | SkSizeof of symbolic_type
  | SkSizeofE of skExpr
  | SkSizeofStr of string
  | SkAlignof of symbolic_type
  | SkAlignofE of skExpr
  | SkCastE of symbolic_type * skExpr
  | SkAddrof of skExpr
  | SkAddrofLabel of Cil.stmt ref
  | SkStartOf of skLVar


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
  | Unit
  (** Base types : only booleans, integers and reals *)
  | Integer
  | Real
  | Boolean
  (** Type tuple *)
  | Tuple of symbolic_type list
  (** Other lifted types *)
  | Bitvector of symbolic_type * int
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
  | CInt of int
  | CReal of float
  | CBool of bool
  | CUnop of symb_unop * constants
  | CBinop of symb_binop * constants * constants
  | CUnsafeUnop of symb_unsafe_unop * constants
  | CUnsafeBinop of symb_unsafe_binop * constants * constants
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



(** ********************************************************** SYMBOLIC TYPES *)

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
