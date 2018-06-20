open Beta
open Fn
open FnPretty
open Format
open Utils

(* Defintiion of a subset of the Dafny language for a cleaner management of
   the proof generation. *)
type type_simple
type type_composed

type _ dafny_basic_type =
  | Int : type_simple dafny_basic_type
  | Real: type_simple dafny_basic_type
  | Bool: type_simple dafny_basic_type
  | Bottom : type_simple dafny_basic_type
  | Sequence: type_simple dafny_basic_type -> type_composed dafny_basic_type


type 'a dfVar = string * 'a dafny_basic_type

and 'a dfFuncDef = type_simple dfVar * 'a dfVar list

and 'a dfProgram =
  | DfFundec : 'a dfVar * _ dfVar list * _ dfExpr -> 'a dfProgram
  | DfJoin : type_simple dfVar * _ dfVar list * _ dfExpr ->
    type_simple dfProgram
  | DfHom : type_simple dfVar * _ dfVar list * _ dfExpr -> type_simple dfProgram

and dfHeader =
  | DfRequire : type_simple dfExpr -> dfHeader
  | DfEnsure : type_simple dfExpr -> dfHeader

and 'a dfExpr =
  | DfEmpty : type_composed dfExpr
  | DfInt : int -> type_simple dfExpr
  | DfBool : bool -> type_simple dfExpr

  | DfFuncall : type_simple dfVar * 'a dfExpr list -> type_simple dfExpr
  | DfVar : 'a dfVar -> 'a dfExpr
  | DfSeqC : type_composed dfVar * type_simple dfExpr -> type_simple dfExpr
  | DfSubSeq : type_composed dfVar * type_simple dfExpr -> type_composed dfExpr
  | DfSeq : type_simple dfExpr -> type_composed dfExpr
  | DfLen : type_composed dfExpr -> type_simple dfExpr

  | DfIte : type_simple dfExpr * 'a dfExpr * 'a dfExpr -> 'a dfExpr

  | DfBinop : 'a dfOp * _ dfExpr * _ dfExpr -> 'a dfExpr
  | DfUnop : 'a dfOp * _ dfExpr -> 'a dfExpr

  | DfSkExpr : fnExpr -> type_simple dfExpr

  | DfCalc : 'a dfExpr * 'a dfExpr * 'a dfExpr -> 'a dfExpr
  | DfAssert : 'a dfExpr -> 'a dfExpr

and 'a dfOp =
  | DfEq : type_simple dfOp
  | DfGeq : type_simple dfOp
  | DfGe : type_simple dfOp
  | DfPlus : type_simple dfOp
  | DfMinus : type_simple dfOp

  | DfConcat : type_composed dfOp
  | DfEqS : type_simple dfOp

  | DfSkBinop : symb_binop -> type_simple dfOp
  | DfSkUnop : symb_unop -> type_simple dfOp


let str_of_op : type a. a dfOp -> string =
  function
  | DfEqS -> "==" | DfEq -> "==" | DfGeq -> ">=" | DfGe -> ">"
  | DfPlus -> "+" | DfMinus -> "-"
  | DfConcat -> "+"
  | DfSkUnop op -> string_of_symb_unop op
  | DfSkBinop op -> string_of_symb_binop op

let rec pp_dfexpr : type a. formatter -> a dfExpr -> unit =
  (fun fmt ->
     function
     | DfEmpty -> fprintf fmt "[]"
     | DfInt i -> fprintf fmt "%i" i
     | DfBool b -> fprintf fmt "%b" b
     | DfFuncall ((fname, ftype), args) ->
       fprintf fmt "@[%s(%a)@]" fname
         (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ", ") pp_dfexpr) args
     | DfVar (vname, vtype) -> fprintf fmt "%s" vname
     | DfSeqC ((seqname, seqtype) , cell_e) ->
       fprintf fmt "%s[%a]" seqname pp_dfexpr cell_e
     | DfSubSeq ((seqname, seqtype), cell_e) ->
       fprintf fmt "%s[..%a]" seqname pp_dfexpr cell_e
     | DfSeq e -> fprintf fmt "[%a]" pp_dfexpr e
     | DfLen e -> fprintf fmt "|%a|" pp_dfexpr e
     | DfIte (c, e1, e2) ->
       fprintf fmt "if@;%a@;{%a}@;else@;{%a}"
         pp_dfexpr c  pp_dfexpr e1 pp_dfexpr e2
     | DfBinop (op, e1, e2) ->
       fprintf fmt "%a@;%s@;%a" pp_dfexpr e1 (str_of_op op) pp_dfexpr e2
     | DfUnop (op, e) ->
       fprintf fmt "%s@;%a" (str_of_op op) pp_dfexpr e
     | DfCalc (lh, asserts, rh) ->
       fprintf fmt "@[%a@\n=={%a}@\n%a@]"
         pp_dfexpr lh pp_dfexpr asserts pp_dfexpr rh
     | DfAssert e ->
       fprintf fmt "assert(%a)" pp_dfexpr e
     | DfSkExpr e -> pp_fnexpr fmt e)

and pp_dfProgram : type a. formatter -> a dfProgram -> unit =
  (fun fmt ->
     function
     | DfFundec ((fname, ty) , func_args, func_body) ->
       fprintf fmt "%s(%a):%a@\n@[<hov 2>{@\n%a@]@\n}"
         (* Name of the function *)
         fname
         (* Arguments of the function: usually, just a list *)
         (fun fmt () -> ()) ()
         (fun fmt () -> ()) ()
         (fun fmt () -> ()) ()


     | DfJoin ((fname, ty), join_args, join_body) ->
       fprintf fmt "%sJoin" fname
     | DfHom ((fname, ty), hom_args, hom_body) ->
       fprintf fmt "Hom%s" fname)

let seq_minus_last s =
  DfSubSeq (s, DfBinop (DfMinus, DfLen (DfVar s), DfInt 1))
