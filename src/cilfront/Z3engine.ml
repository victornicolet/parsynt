open Cil
open SketchTypes
open Utils
open Z3
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Sort
open Z3.Boolean
open Z3.FuncDecl
open Z3.Expr
open Z3.Solver

let unsupported = failwith "! Z3 : unsupported !"

class engine (sctx : SketchTypes.context) =
  object(self)
    val var_exprs = IH.create 10
    val variables = IH.create 10
    val array_funcs = IH.create 10
    val ctx = mk_context [("model", "true"); ("proof", "false")]
    val sctx = sctx

    method start () =
      self#load_symbols;
      ()

    method private load_symbols =
      let intsort = Integer.mk_sort ctx in
      let boolsort = Boolean.mk_sort ctx in
      VS.iter
        (fun vi ->
           IH.add variables vi.vid vi;
           match type_of_ciltyp vi.vtype with
           | Integer ->
             IH.add var_exprs vi.vid
               (Expr.mk_const ctx (Symbol.mk_string ctx vi.vname) (intsort))

           | Boolean ->
             IH.add var_exprs vi.vid
               (Expr.mk_const ctx (Symbol.mk_string ctx vi.vname) boolsort)

           | Vector (st, _) ->
             (* Just go to two dimensional arrays, and model them with
                uninterpreted functions. *)
             (match st with
              | Integer ->
                IH.add array_funcs vi.vid
                  (mk_func_decl_s ctx vi.vname [intsort] (intsort))

              | Boolean ->
                IH.add array_funcs vi.vid
                  (mk_func_decl_s ctx vi.vname [intsort] (boolsort))

              | Vector (Integer, _) ->
                IH.add array_funcs vi.vid
                  (mk_func_decl_s ctx vi.vname [intsort; intsort] (intsort))

              | Vector (Boolean, _) ->
                IH.add array_funcs vi.vid
                  (mk_func_decl_s ctx vi.vname [intsort; intsort] (boolsort))

              | _ -> unsupported)

           | _ -> unsupported)
        sctx.all_vars


    method make_model (expr : skExpr) =
      match expr with
      | SkBinop (op, e1, e2) ->
        let me1 = self#make_model e1 in
        let me2 = self#make_model e2 in
        let ops = [me1; me2] in
        (match op with
         | Plus -> mk_add ctx ops
         | Minus -> mk_sub ctx ops
         | Times -> mk_mul ctx ops
         | Div -> mk_div ctx me1 me2
         | And -> mk_and ctx ops
         | Or -> mk_or ctx ops
         | Max -> mk_ite ctx (mk_gt ctx me1 me2) me1 me2
         | Min -> mk_ite ctx (mk_lt ctx me1 me2) me1 me2
         | Eq -> mk_eq ctx me1 me2
         | Gt -> mk_gt ctx me1 me2
         | Lt -> mk_lt ctx me1 me2
         | Ge -> mk_ge ctx me1 me2
         | Le -> mk_le ctx me1 me2
         | _ -> unsupported)

      | SkUnop (op, e) ->
        let me = self#make_model e in
        (match op with
         | Add1 -> mk_add ctx [me;(mk_numeral_i ctx 1)]
         | Sub1 -> mk_sub ctx [me;(mk_numeral_i ctx 1)]
         | Neg -> mk_unary_minus ctx me
         | Not -> mk_not ctx me
         | _ -> unsupported)

      | SkQuestion (c, e1, e2) ->
        mk_ite ctx (self#make_model c) (self#make_model e1) (self#make_model e2)

      | SkVar v -> self#make_model_sklvar  v

      | _ -> unsupported

    (**
       Arrays are uninterpreted functions. Match directly one or two dimensions,
       they are then modelled by uninterpeted function taking one or two integer
       args.
       Simple variables have been stored previously in the variable id -> expression
       of variable mappings.
    *)
    method private make_model_sklvar v =
      match v with
      | SkVarinfo vi -> IH.find var_exprs vi.vid

      | SkArray (SkArray(lvar, offset0), offset) ->
        mk_app ctx (self#find_array_function lvar)
          [self#make_model offset0; self#make_model offset]

      | SkArray (lvar, offset) ->
        mk_app ctx (self#find_array_function lvar) [self#make_model offset]

      | _ -> unsupported

    (**
       Simple lookup, with unsuppported exception if the input lvar is not a simple
       varinfo container.
    *)
    method private find_array_function lvar =
      let vi = check_option (vi_of lvar) in
      IH.find array_funcs vi.vid

  end
