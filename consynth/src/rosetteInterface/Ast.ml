open RUtils

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

let op_to_string = function
  | Plus -> "+"
  | Minus -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
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
  | Load -> "load"

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

let rec to_string (e : expr) : string =
  let rec cons_to_string (x : expr) : string list =
    match x with
    | Nil_e -> []
    | Cons_e (x, y) -> to_string x :: cons_to_string y
    | y -> ["."; to_string y]
  in
    match e with
    | Int_e n -> string_of_int n
    | Str_e s -> s
    | Bool_e b -> string_of_bool b
    | Id_e x -> x
    | Nil_e -> "()"
    | Cons_e _ -> listify (cons_to_string e)
    | Let_e (x, e1, e2) ->
        let s1 = to_string e1
        and s2 = to_string e2
        in listify ["let"; x; s1; s2]
    | Letrec_e (x, e1, e2) ->
        let s1 = to_string e1
        and s2 = to_string e2
        in listify ["letrec"; x; s1; s2]
    | If_e (e0, e1, e2) ->
        let s0 = to_string e0
        and s1 = to_string e1
        and s2 = to_string e2
        in listify ["if"; s0; s1; s2]
    | Apply_e (e1, e2) ->
        let s1 = to_string e1 in
        let s2 = String.concat " " (List.map to_string e2)
        in listify [s1; s2]
    | Fun_e (xs, e) ->
      listify ("lambda" :: listify_mult xs :: [to_string e])
    | Def_e (xs, e) ->
      listify ("define" :: listify_mult xs :: [to_string e])
    | Defrec_e (xs, e) ->
      listify ("definerec" :: listify_mult xs :: [to_string e])
    | Binop_e (op, e1, e2) ->
        let s0 = op_to_string op
        and s1 = to_string e1
        and s2 = to_string e2
        in listify [s0; s1; s2]
    | Unop_e (op, e) ->
        let s0 = op_to_string op
        and s1 = to_string e
        in listify [s0; s1]
    | Delayed_e (ex) -> "delay " ^ to_string ex
    | Forced_e (ex) -> to_string ex
