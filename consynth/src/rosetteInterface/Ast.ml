open RUtils
open Format

type id = string

type op =
  | Plus
  | Minus
  | Mul
  | Div
  | Mod
  | Eq
  | Neq
  | Lt
  | Leq
  | Gt
  | Geq
  | And
  | Or
  | Not
  | Car
  | Cdr
  | Null
  | Load

let pp_op fmt op =
  fprintf fmt "%s"
    (match op with
     | Plus -> "+"
     | Minus -> "-"
     | Mul -> "*"
     | Div -> "/"
     | Mod -> "\\%"
     | Eq -> "="
     | Neq -> "!="
     | Lt -> "<"
     | Leq -> "<="
     | Gt -> ">"
     | Geq -> ">="
     | And -> "&"
     | Or -> "|"
     | Not -> "~"
     | Car -> "car"
     | Cdr -> "cdr"
     | Null -> "null"
     | Load -> "load")

type expr =
  | Int_e of int
  | Str_e of string
  | Bool_e of bool
  | Id_e of id
  | Nil_e
  | Cons_e of expr * expr
  | Let_e of id * expr * expr
  | Letrec_e of id * expr * expr
  | If_e of expr * expr * expr
  | Apply_e of expr * expr list
  | Fun_e of id list * expr
  | Def_e of id list * expr
  | Defrec_e of id list * expr
  | Binop_e of op * expr * expr
  | Unop_e of op * expr
  | Delayed_e of expr
  | Forced_e of expr

let sep_space fmt () = fprintf fmt " "

let rec pp_expr fmt e =
  let rec pp_cons fmt x =
    fprintf fmt "%a"
      (fun fmt' ex ->
         (match ex with
           | Nil_e -> fprintf fmt' "%s" "()"
           | Cons_e (x, y) -> fprintf fmt' "(%a %a)" pp_expr x pp_expr y
           | y ->  fprintf fmt' "%s" "()")) x
  in
    match e with
    | Int_e n -> pp_print_int fmt n
    | Str_e s -> fprintf fmt "\"%s\"" s
    | Bool_e b -> pp_print_bool fmt b
    | Id_e x -> pp_print_string fmt x
    | Nil_e -> pp_print_string fmt "()"
    | Cons_e _ -> pp_cons fmt e
    | Let_e (x, e1, e2) ->
      fprintf fmt "(let ([%s %a]) %a)" x pp_expr e1 pp_expr e2
    | Letrec_e (x, e1, e2) ->
      fprintf fmt "(letrec ([%s %a]) %a)" x pp_expr e1 pp_expr e2
    | If_e (e0, e1, e2) ->
      fprintf fmt "(if %a %a %a)" pp_expr e0 pp_expr e1 pp_expr e2
    | Apply_e (e1, e2) ->
      fprintf fmt "(%a %a)" pp_expr e1
        (fun fmt l ->
           pp_print_list ~pp_sep:sep_space
             pp_expr fmt l) e2
    | Fun_e (xs, e) ->
      fprintf fmt "(lambda (%a) %a)"
        (fun fmt l -> pp_print_list ~pp_sep:sep_space pp_print_string fmt l) xs
        pp_expr e

    | Def_e (xs, e) ->
      fprintf fmt "(define (%a) %a)"
        (fun fmt l -> pp_print_list ~pp_sep:sep_space pp_print_string fmt l) xs
        pp_expr e

    | Defrec_e (xs, e) ->
      fprintf fmt "(define (%a) %a)"
        (fun fmt l -> pp_print_list ~pp_sep:sep_space pp_print_string fmt l) xs
        pp_expr e

    | Binop_e (op, e1, e2) ->
      fprintf fmt "(%a %a %a)" pp_op op pp_expr e1 pp_expr e2
    | Unop_e (op, e) ->
      fprintf fmt "(%a %a)" pp_op op pp_expr e
    | Delayed_e (ex) -> fprintf fmt "delay %a" pp_expr ex
    | Forced_e (ex) -> pp_expr fmt ex
