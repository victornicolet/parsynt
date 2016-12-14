open Z3
open Z3.Boolean
open Z3.Arithmetic
open Z3.Z3Array
open Z3.Expr


open Format
open SketchTypes
open SPretty
open Utils
open Cil

let default_context = mk_context []

(** - Choose double preicision for all reals/numerals.
    - The domain of the arrays is always the integers. *)
let rec sort_of_sty ctx =
  function
  | Boolean -> Boolean.mk_sort ctx
  | Integer -> Integer.mk_sort ctx
  | Real -> Real.mk_sort ctx
  | Num -> Real.mk_sort ctx
  | Vector (t, _) -> Z3Array.mk_sort ctx
                       (sort_of_sty ctx Integer) (sort_of_sty ctx t)
  | _ as t->
    eprintf "Type %a is unspported." pp_typ t;
    failwith "Unsupported type in Z3 model building."

let map_of_consts ctx vars =
  VS.fold
    (fun vi vi_map ->
       let varsymb = Symbol.mk_string ctx vi.vname in
       let sty = symb_type_of_ciltyp vi.vtype in
       IM.add vi.vid (mk_const ctx varsymb (sort_of_sty ctx sty)) vi_map
    ) vars IM.empty

let rec of_expr ctx vars e =
  match e with
  | SkVar v -> of_var ctx vars v
  | SkConst c -> of_const ctx vars c
  | SkBinop (op, e1, e2) ->
    let exprs = [of_expr ctx vars e1; of_expr ctx vars e2] in
    begin
      match op with
      (* Artihmetic *)
      | Plus -> mk_add ctx exprs
      | Minus -> mk_sub ctx exprs
      | Times -> mk_mul ctx exprs
      | Div -> mk_div ctx (List.nth exprs 0) (List.nth exprs 1)
      | Expt -> mk_power ctx (List.nth exprs 0) (List.nth exprs 1)
      (* Booleans *)
      | And -> mk_and ctx exprs
      | Or -> mk_or ctx exprs
      | Nand -> mk_not ctx (mk_and ctx exprs)
      | Nor -> mk_not ctx (mk_or ctx exprs)
      | Xor -> mk_xor ctx (List.nth exprs 0) (List.nth exprs 1)
      | Implies -> mk_implies ctx (List.nth exprs 0) (List.nth exprs 1)
      (* Comparisons *)
      | Lt -> mk_lt ctx (List.nth exprs 0) (List.nth exprs 1)
      | Le -> mk_le ctx (List.nth exprs 0) (List.nth exprs 1)
      | Gt -> mk_gt ctx (List.nth exprs 0) (List.nth exprs 1)
      | Ge -> mk_lt ctx (List.nth exprs 0) (List.nth exprs 1)
      | Eq -> mk_eq ctx (List.nth exprs 0) (List.nth exprs 1)
      | Neq -> mk_not ctx (mk_eq ctx (List.nth exprs 0) (List.nth exprs 1))
      (* Max. min *)
      | Max -> mk_ite ctx (mk_gt ctx (List.nth exprs 0) (List.nth exprs 1))
                 (List.nth exprs 0) (List.nth exprs 1)
      | Min -> mk_ite ctx (mk_gt ctx (List.nth exprs 0) (List.nth exprs 1))
                 (List.nth exprs 1) (List.nth exprs 0)

      (* Quot, Rem, Mod, SHiftL, SHiftR *)
      | _ -> failwith "Unsupported binary operator"
    end
  | SkUnop (op, e) ->
    let expr = of_expr ctx vars e in
    begin
      match op with
      | Not -> mk_not ctx expr
      | Neg -> mk_unary_minus ctx expr
      | Add1 -> mk_add ctx [expr; Integer.mk_numeral_i ctx 1]
      | Sub1 -> mk_sub ctx [expr; Integer.mk_numeral_i ctx 1]
      | Floor | Abs -> FloatingPoint.mk_abs ctx
                         (FloatingPoint.mk_to_real ctx expr)
      | _ -> failwith "Unsupported unary"
    end

  | SkQuestion (c, a, b) ->
    mk_ite ctx (of_expr ctx vars c)
      (of_expr ctx vars a)
      (of_expr ctx vars b)

  | _ -> failwith "Unimplemented"

and of_var ctx vars v =
  match v with
  | SkVarinfo vi ->
    begin
    try
      IM.find vi.vid vars
    with Not_found ->
      (eprintf "Variable %s not found while building model." vi.vname;
       raise Not_found)
    end
  | SkArray (a, i) ->
    mk_select ctx (of_var ctx vars a) (of_expr ctx vars i)

  | SkTuple _ ->
    failwith "Unsupported Tuples"

and of_const ctx c =
  match c with
  | CInt i -> Integer.mk_numeral_i ctx i
