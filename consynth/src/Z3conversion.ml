open Z3
open Z3enums
open Z3.Boolean
open Z3.Arithmetic
open Z3.Z3Array
open Z3.Expr

open Cil
open Expressions
open Format
open SketchTypes
open SPretty
open Utils


let default_context = mk_context []

let get_const_vid e =
  FuncDecl.get_id (Expr.get_func_decl e)

(** - Choose double preicision for all reals/numerals.
    - The domain of the arrays is always the integers. *)
let rec sort_of_sty ctx =
  function
  | Boolean -> Boolean.mk_sort ctx
  | Integer -> Integer.mk_sort ctx
  | Real -> FloatingPoint.mk_sort_double ctx
  | Num ->  FloatingPoint.mk_sort_double ctx
  | Vector (t, _) -> Z3Array.mk_sort ctx
                       (sort_of_sty ctx Integer) (sort_of_sty ctx t)
  | _ as t->
    eprintf "Type %a is unspported." pp_typ t;
    failwith "Unsupported type in Z3 model building."

let sty_of_sort =
  function
  | INT_SORT -> Some Integer
  | BOOL_SORT -> Some Boolean
  | REAL_SORT -> Some Real
  | RE_SORT -> Some Real
  | FLOATING_POINT_SORT -> Some Real
  | BV_SORT -> None
  | ARRAY_SORT -> None
  | UNKNOWN_SORT -> Some Bottom
  | _ -> failwith "Unsupported sort in expression translation."


let create_vars_map ?(ctx = default_context) vars =
    VS.fold
      (fun vi (vi_map, z3_vid_map) ->
         let varsymb = Symbol.mk_string ctx vi.vname in
         let sty = symb_type_of_ciltyp vi.vtype in
         let z3var = (mk_const ctx varsymb (sort_of_sty ctx sty)) in
         (IM.add vi.vid z3var vi_map,
          IM.add (get_const_vid z3var) vi z3_vid_map)
      ) vars (IM.empty, IM.empty)



(** Translate sketch expressions to Z3 Expressions
    @param ctx The context required by Z3.
    @param vars A map from Cil's variable ids to expressions for these variable
    in Z3.
    @param e The sketch expression to translate.
    @return The corresponding expression in Z3.
*)

let rec of_expr ctx vars e =
  match e with
  | SkVar v -> of_var ctx vars v
  | SkConst c -> of_const ctx c
  | SkBinop (op, e1, e2) ->
    let exprs = [of_expr ctx vars e1; of_expr ctx vars e2] in
    begin
      match op with
      (* Artihmetic *)
      | Plus -> mk_add ctx exprs
      | Minus -> mk_sub ctx exprs
      | Times -> mk_mul ctx exprs
      | Div -> mk_div ctx (exprs >> 0) (exprs >> 1)
      | Expt -> mk_power ctx (exprs >> 0) (exprs >> 1)
      (* Booleans *)
      | And -> mk_and ctx exprs
      | Or -> mk_or ctx exprs
      | Nand -> mk_not ctx (mk_and ctx exprs)
      | Nor -> mk_not ctx (mk_or ctx exprs)
      | Xor -> mk_xor ctx (exprs >> 0) (exprs >> 1)
      | Implies -> mk_implies ctx (exprs >> 0) (exprs >> 1)
      (* Comparisons *)
      | Lt -> mk_lt ctx (exprs >> 0) (exprs >> 1)
      | Le -> mk_le ctx (exprs >> 0) (exprs >> 1)
      | Gt -> mk_gt ctx (exprs >> 0) (exprs >> 1)
      | Ge -> mk_lt ctx (exprs >> 0) (exprs >> 1)
      | Eq -> mk_eq ctx (exprs >> 0) (exprs >> 1)
      | Neq -> mk_not ctx (mk_eq ctx (exprs >> 0) (exprs >> 1))
      (* Max. min *)
      | Max -> mk_ite ctx (mk_gt ctx (exprs >> 0) (exprs >> 1))
                 (exprs >> 0) (exprs >> 1)
      | Min -> mk_ite ctx (mk_gt ctx (exprs >> 0) (exprs >> 1))
                 (exprs >> 1) (exprs >> 0)

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
  | CBool b -> if b then Boolean.mk_true ctx else Boolean.mk_false ctx
  | CReal r -> FloatingPoint.mk_numeral_f ctx r (Real.mk_sort ctx)
  | CChar c -> failwith "Char unsupported."
  | CString s -> failwith "String unsupported."
  | _ -> failwith "Constant type unsupported."


let make_z3 ?(ctx = default_context) = of_expr ctx


let simplify_z3 ?(ctx = default_context) e =
  let params = Params.mk_params ctx in
  Params.add_bool params (Symbol.mk_string ctx "pull_cheap_ite") true;
  Params.add_bool params (Symbol.mk_string ctx "ite_extra_rules") true;
  Expr.simplify e (Some params)

(** Translate a Z3 expression into a sketch expression.
    @param vars A map from Z3 function ids to the corresponding varinfo.
    @param e The expression in Z3 to translate.
    @return The corresponding SKetch expression
*)

let rec from_expr vars e =
  if Expr.is_const e then
    SkVar(from_const vars e)
  else
    (if Expr.is_numeral e then
       SkConst (from_numeral e)
     else
       from_fundecl vars e)

and from_const vars e =
  (** A const is a function with arity 0 and empty domain. Since*)
  let z3_vid = FuncDecl.get_id (Expr.get_func_decl e) in
  SkVarinfo (IM.find z3_vid vars)

and from_numeral e =
  let sort = (Expr.get_sort e) in
  let styp = sty_of_sort (Sort.get_sort_kind sort) in
  match styp with
  | Some non_composite_sort ->
    begin
      match non_composite_sort with
      | Boolean ->
        CBool
          (match Boolean.get_bool_value e with
           | L_FALSE -> false
           | L_TRUE -> true
           | L_UNDEF -> failwith "Undefined boolean value in from_numeral.")
      | Integer -> CInt (Integer.get_int e)
      | Real ->
        (** Method 1 : get significand and exponent, on compute the float
            let exp = FloatingPoint.get_ebits ctx sort in
            let significand = FloatingPoint.get_sbits ctx sort in
            (foi significand) *. (10. ** (foi exp))**)
        (** Method 2 : get the float from the string representation *)
        CReal (float_of_string (FloatingPoint.numeral_to_string e))
      | _ -> failwith "Not a non-composite sort."
    end
  | None ->
    failwith "Non a numeral sort"

and from_fundecl vars e =
  let fundecl = Expr.get_func_decl e in
  let args = Expr.get_args e in
  match FuncDecl.get_arity fundecl with
  | 0 -> failwith "Don't know any 0 ops"
  | 1 -> SkUnop (check_option (get_unop fundecl),
                 from_expr vars (args >> 0))
  | 2 ->
    begin
      match get_binop fundecl with
      | Some op ->
        SkBinop (op, from_expr vars (args >> 0), from_expr vars (args >> 1))
      (** With two arguments, could still be an array access *)
      | None ->
        let dkind = FuncDecl.get_decl_kind fundecl in
        match dkind with
        (** Array access is a fundecl with two parameters, the array variable
            and the index, see api_array.cpp *)
        | OP_SELECT -> SkVar (SkArray (from_const vars (args >> 0),
                                       from_expr vars (args >> 1)))
        | _ -> failwith "Binary operation not recognized."
    end
  | 3 -> SkQuestion (from_expr vars (args >> 0),
                     from_expr vars (args >> 1),
                     from_expr vars (args >> 2))
(** TODO : and is not a binary op, we have to rebuild the tree after.
    I think the solution is already in the flat AC form of the reduction *)
  | _ ->
    match get_binop fundecl with
    | Some op ->
      begin
        try
          let opname = get_AC_op op in
          SkApp (Integer, Some opname,
                 (List.map (fun e -> from_expr vars e) args))
        with Not_found ->
          (eprintf "Failure to convert %s@." (Expr.to_string e);
           failwith "Failed to convert expression.")
      end
    | None ->
      (eprintf "Failure to convert %s@." (Expr.to_string e);
       failwith "Failed to convert expression.")



and get_unop fundecl =
  match FuncDecl.get_decl_kind fundecl with
  | OP_NOT | OP_BNEG -> Some Not
  | OP_FPA_NEG | OP_UMINUS -> Some Neg
  | OP_FPA_SQRT -> Some (UnsafeUnop Sqrt)
  | _ -> None

and get_binop fundecl =
  match FuncDecl.get_decl_kind fundecl with
  (** Artihmetic *)
  | OP_ADD | OP_FPA_ADD -> Some Plus
  | OP_SUB | OP_FPA_SUB -> Some Minus
  | OP_MUL | OP_FPA_MUL -> Some Times
  | OP_DIV | OP_FPA_DIV -> Some Div
  | OP_POWER -> Some Expt
  | OP_AND | OP_BAND -> Some And
  | OP_OR | OP_BOR -> Some Or
  (** Comparisons *)
  | OP_EQ -> Some Eq
  | OP_FPA_LE | OP_LE -> Some Le
  | OP_FPA_LT | OP_LT -> Some Lt
  | OP_FPA_GE | OP_GE -> Some Ge
  | OP_FPA_GT | OP_GT -> Some Gt
  | OP_XOR -> Some Xor
  | _ -> None


(** Wrap translation functions and helpers in an object *)

class z3Translator vars =
  let z3v, varm = create_vars_map vars in
  object (self)
    val mutable initial_varset = vars
    val mutable z3vars = z3v
    val mutable skvars = varm
    val mutable context = mk_context []
    method expr_to_z3 e = of_expr context  e
  end
