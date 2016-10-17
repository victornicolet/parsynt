open Utils
open Format
open Findloops
open Ast

let use_unsafe_operations = ref false


(** Internal type for building sketches *)

type sklet =
  | SkLetExpr of (skLVar * skExpr) list
  (**  (let ([var expr]) let)*)
  | SkLetIn of (skLVar * skExpr) list * sklet

and skLVar =
  | SkState
  | SkVarinfo of Cil.varinfo
  (** Access to an array cell *)
  | SkArray of skLVar * skExpr

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
  SkLetExpr ([SkState, SkVar (SkState)])


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
   constants.
*)
let mkVar ?(offsets = []) vi =
  match c_constant vi.Cil.vname with
  | Some c -> SkConst c
  | None ->
	 let var =
       List.fold_left
	     (fun sklvar offset ->
           SkArray (sklvar, offset))
	     (SkVarinfo vi)
         offsets
     in SkVar var

let rec cmpVar sklvar1 sklvar2 =
  match sklvar1, sklvar2 with
  | SkState, SkState -> 0
  | SkVarinfo vi, SkVarinfo vi' -> compare vi.Cil.vid vi'.Cil.vid
  | SkArray (sklv1, _), SkArray (sklv2, _) ->
     cmpVar sklv1 sklv2
  | SkState, _ -> 1
  | _ , SkState -> -1
  | SkArray _ , _ -> 1
  | _ , SkArray _ -> -1

let rec vi_of sklv =
  match sklv with
  | SkState -> None
  | SkVarinfo vi' -> Some vi'
  | SkArray (sklv', _) -> vi_of sklv'

let is_vi sklv vi = maybe_apply_default (fun x -> vi = x) (vi_of sklv)


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


(** ********************************************************** SYMBOLIC TYPES *)

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


(** *********************************************** Recursion in expresssions *)

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
      List.fold_left (fun acc (v, e) -> join acc (recurse_aux e)) init velist

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
    | e when case e -> case_handler recurse_aux e
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


(** Compose a function by adding new assignments *)
let compose_head assignments func =
  SkLetIn (assignments, func)

let rec compose_tail assignments func =
  match func with
  | SkLetExpr el ->
    SkLetIn (el, SkLetExpr assignments)
  | SkLetIn (el, l) -> compose_tail assignments l


(** Replace expressions by a variables *)
let replace_subexpr_in to_replace var expr =
  transform_expr
    (fun e -> e = to_replace)
    (fun f e -> SkVar (SkVarinfo var))
    identity
    identity
    expr


(** Translate basic scheme to the Sketch expressions
    @param env a mapping from variable ids to varinfos.
*)
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

let rec scm_to_sk env scm =
  try
    match scm with
    | Int_e i -> None, Some (SkConst (CInt i))
    | Str_e s -> None, Some (SkConst (CString s))
    | Bool_e b -> None, Some (SkConst (CBool b))
    | Id_e id -> None, Some (SkVar (SkVarinfo (SM.find id env)))
    | Nil_e -> None, Some (SkConst (CNil))

    | Binop_e (op, e1, e2) ->
      let _, e1' = scm_to_sk env e1 in
      let _, e2' = scm_to_sk env e2 in
      None, Some (SkBinop (get_binop_of_scm op, co e1', co e2'))

    | Unop_e (op, e) ->
      let _, e' = scm_to_sk env e in
      None, Some (SkUnop (get_unop_of_scm op, co e'))

    | Cons_e (x, y)-> failwith "Cons not supported"

    | Let_e (bindings, e2)
    | Letrec_e (bindings, e2) ->
      let bds = List.map
          (fun (ids, e) ->
             let _, exp = scm_to_sk env e in
             (SkVarinfo (SM.find ids env)), co exp)
          bindings
      in
      let sk_let, _ = scm_to_sk env e2 in
      Some (SkLetIn (bds, co sk_let)), None

    | If_e (c, e1, e2) ->
      let _, cond = scm_to_sk env c in
      let le1, ex1 = scm_to_sk env e1 in
      let le2, ex2 = scm_to_sk env e2 in
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
      failwith "TODO"

    | Fun_e _ | Def_e _ | Defrec_e _ |Delayed_e _ | Forced_e _ ->
      failwith "Not supported"

  with Not_found ->
    failwith "Variable name not found in current environment."



module ES = Set.Make (
  struct
    let compare = Pervasives.compare
    type t = skExpr
  end)
