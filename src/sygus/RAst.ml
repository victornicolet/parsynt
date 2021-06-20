open Fmt

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
  | Min
  | Max
  | Null
  | Load

let pp_op fmt op =
  pf fmt "%s"
    (match op with
    | Plus -> "+"
    | Minus -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Mod -> "mod"
    | Eq -> "="
    | Neq -> "!="
    | Lt -> "<"
    | Leq -> "<="
    | Gt -> ">"
    | Geq -> ">="
    | And -> "&&"
    | Or -> "||"
    | Not -> "not"
    | Min -> "min"
    | Max -> "max"
    | Car -> "car"
    | Cdr -> "cdr"
    | Null -> "null"
    | Load -> "load")

type expr =
  | Int_e of int
  | Float_e of float
  | Str_e of string
  | Bool_e of bool
  | Id_e of id
  | Nil_e
  | Cons_e of expr * expr
  | Let_e of (id * expr) list * expr
  | Letrec_e of (id * expr) list * expr
  | If_e of expr * expr * expr
  | Apply_e of expr * expr list
  | Fun_e of id list * expr
  | Def_e of id list * expr
  | Defrec_e of id list * expr
  | Binop_e of op * expr * expr
  | Unop_e of op * expr
  | Delayed_e of expr
  | Forced_e of expr

let sep_space fmt () = pf fmt " "

let rec pp_expr fmt e =
  let pp_cons fmt x =
    pf fmt "%a"
      (fun fmt' ex ->
        match ex with
        | Nil_e -> pf fmt' "%s" "()"
        | Cons_e (x, y) -> pf fmt' "(%a %a)" pp_expr x pp_expr y
        | _ -> pf fmt' "%s" "()")
      x
  in
  match e with
  | Int_e n -> int fmt n
  | Float_e f -> float fmt f
  | Str_e s -> pf fmt "\"%s\"" s
  | Bool_e b -> bool fmt b
  | Id_e x -> string fmt x
  | Nil_e -> string fmt "()"
  | Cons_e _ -> pp_cons fmt e
  | Let_e (bindings, e2) ->
      pf fmt "(let (%a) %a)"
        (fun fmt l -> list ~sep:sep_space (fun fmt (i, e) -> pf fmt "[%s %a]" i pp_expr e) fmt l)
        bindings pp_expr e2
  | Letrec_e (bindings, e2) ->
      pf fmt "(letrec (%a) %a)"
        (fun fmt l -> list ~sep:sep_space (fun fmt (i, e) -> pf fmt "[%s %a]" i pp_expr e) fmt l)
        bindings pp_expr e2
  | If_e (e0, e1, e2) -> pf fmt "(if %a %a %a)" pp_expr e0 pp_expr e1 pp_expr e2
  | Apply_e (e1, e2) ->
      pf fmt "(%a %a)" pp_expr e1 (fun fmt l -> list ~sep:sep_space pp_expr fmt l) e2
  | Fun_e (xs, e) ->
      pf fmt "(lambda (%a) %a)" (fun fmt l -> list ~sep:sep_space string fmt l) xs pp_expr e
  | Def_e (xs, e) ->
      pf fmt "(define (%a) %a)" (fun fmt l -> list ~sep:sep_space string fmt l) xs pp_expr e
  | Defrec_e (xs, e) ->
      pf fmt "(define (%a) %a)" (fun fmt l -> list ~sep:sep_space string fmt l) xs pp_expr e
  | Binop_e (op, e1, e2) -> pf fmt "(%a %a %a)" pp_op op pp_expr e1 pp_expr e2
  | Unop_e (op, e) -> pf fmt "(%a %a)" pp_op op pp_expr e
  | Delayed_e ex -> pf fmt "delay %a" pp_expr ex
  | Forced_e ex -> pp_expr fmt ex

let pp_expr_list fmt l =
  list ~sep:(fun fmt () -> pf fmt "@.") pp_expr fmt l;
  pf fmt "@."

let identity x = x

type ast_transformer = {
  t_expr : (expr -> expr) -> expr -> expr option;
  t_const : expr -> expr;
  t_id : expr -> expr;
}

let transform (t : ast_transformer) (e : expr) : expr =
  let rec aux_t e =
    match t.t_expr aux_t e with
    | Some e' -> e'
    | None -> (
        match e with
        | Id_e _ -> t.t_id e
        | Bool_e _ | Float_e _ | Int_e _ | Str_e _ | Nil_e -> t.t_const e
        | Binop_e (op, e1, e2) -> Binop_e (op, aux_t e1, aux_t e2)
        | Unop_e (op, e0) -> Unop_e (op, aux_t e0)
        | Forced_e e0 -> Forced_e (aux_t e0)
        | Delayed_e e0 -> Delayed_e (aux_t e0)
        | Cons_e (e1, e2) -> Cons_e (aux_t e1, aux_t e2)
        | If_e (c, e1, e2) -> If_e (aux_t c, aux_t e1, aux_t e2)
        (* Functional forms *)
        | Let_e (se_list, e) -> Let_e (List.map (fun (s, e) -> (s, aux_t e)) se_list, aux_t e)
        | Letrec_e (se_list, e) -> Letrec_e (List.map (fun (s, e) -> (s, aux_t e)) se_list, aux_t e)
        | Def_e (sl, e) -> Def_e (sl, aux_t e)
        | Defrec_e (sl, e) -> Defrec_e (sl, aux_t e)
        | Apply_e (e, el) -> Apply_e (aux_t e, List.map aux_t el)
        | Fun_e (sl, e) -> Fun_e (sl, aux_t e))
  in
  aux_t e

exception AstEval of string

let exn_eval s = raise (AstEval s)

exception AstArith

let exn_arith () = raise AstArith

exception AstCompar

let exn_comp () = raise AstCompar

exception AstLogic

let exn_logic () = raise AstLogic

let apply_int op i1 i2 =
  try
    try
      Int_e
        (match op with
        | Plus -> i1 + i2
        | Minus -> i1 - i2
        | Mul -> i1 * i2
        | Div -> i1 / i2
        | Mod -> i1 mod i2
        | Max -> max i1 i2
        | Min -> min i1 i2
        | _ -> exn_arith ())
    with AstArith ->
      Bool_e
        (match op with
        | Eq -> i1 = i2
        | Neq -> i1 != i2
        | Gt -> i1 > i2
        | Lt -> i1 < i2
        | Geq -> i1 >= i2
        | Leq -> i1 <= i2
        | _ -> exn_comp ())
  with AstCompar | AstArith -> exn_eval "Bad operator for two integers."

let apply_float op f1 f2 =
  try
    try
      Float_e
        (match op with
        | Plus -> f1 +. f2
        | Minus -> f1 -. f2
        | Mul -> f1 *. f2
        | Div -> f1 /. f2
        | Max -> max f1 f2
        | Min -> min f1 f2
        | _ -> exn_arith ())
    with AstArith ->
      Bool_e
        (match op with
        | Eq -> f1 = f2
        | Neq -> f1 != f2
        | Gt -> f1 > f2
        | Lt -> f1 < f2
        | Geq -> f1 >= f2
        | Leq -> f1 <= f2
        | _ -> exn_comp ())
  with AstCompar | AstArith -> exn_eval "Bad operator for two floats."

let apply_bool op b1 b2 =
  try
    Bool_e
      (match op with
      | And -> b1 && b2
      | Or -> b1 || b2
      | Eq -> b1 = b2
      | Neq -> b1 != b2
      | _ -> exn_logic ())
  with AstLogic -> exn_eval "Bad operator for two bools."
