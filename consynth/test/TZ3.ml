open Format
open PpHelper
open SPretty
open Utils
open Z3
open Z3.Expr
open Z3.Params
open Z3.Symbol
open Z3.Boolean



let test_z3_api (ctx : context) =
  let params = mk_params ctx in
  add_bool params (mk_string ctx "pull_cheap_ite") true;
  add_bool params (mk_string ctx "ite_extra_rules") true;
  let a = (Expr.mk_const ctx (Symbol.mk_string ctx "x")
             (Boolean.mk_sort ctx))
  in
  let b = (Expr.mk_const ctx (Symbol.mk_string ctx "y")
             (Boolean.mk_sort ctx))
  in
  let c1 = (Expr.mk_const ctx (Symbol.mk_string ctx "c1")
             (Boolean.mk_sort ctx))
  in
  let c2 =(Expr.mk_const ctx (Symbol.mk_string ctx "c2")
             (Boolean.mk_sort ctx))
  in
  let itee =
    mk_ite ctx c1 (mk_ite ctx c2 (mk_ite ctx c2 a b) b) (mk_ite ctx (mk_not ctx c1) b a)
  in
  print_endline (Expr.get_simplify_help ctx);
  printf "Initially : %s@." (Expr.to_string itee);
  let itee_simpl =
    Expr.simplify itee (Some params)
  in
  printf "Simplified : %s@." (Expr.to_string itee_simpl);
  (** Testing parsing back to some type *)
  let expr_args = Expr.get_args itee_simpl in
  let expr_fund = Expr.get_func_decl itee_simpl in
  printf "Args : %a@."
    (fun fmt li -> ppli fmt ~sep:", " (fun fmt e -> fprintf fmt "%s" (Expr.to_string e)) li)
    expr_args;
  printf "Func decl: %s@."
    (FuncDecl.to_string expr_fund);
  (if (FuncDecl.get_decl_kind expr_fund) = Z3enums.OP_ITE then
     printf "Is ite, OK.@."
   else
     printf "Not ite, FAIL.@.");
  let condition = expr_args >> 0 in
  let ae = expr_args >> 1 in
  let be = expr_args >> 2 in
  printf "Is %s a const ? %b.@." (Expr.to_string condition) (Expr.is_const condition);
  let cond_args = Expr.get_args condition in
  printf "Operator : %i with args %s, %s@."
    (FuncDecl.get_id (Expr.get_func_decl condition))
    (Expr.to_string (cond_args >> 0))
    (Expr.to_string (cond_args >> 1));
  printf "Is %s a const ? %b.@." (Expr.to_string ae) (Expr.is_const ae);
  printf "Is %s a const ? %b.@." (Expr.to_string be) (Expr.is_const be);;

open Z3conversion
open SketchTypes
open TestUtils

let test_sketch_translation () =
  (** Declare variables *)
  let vm = new variableManager
    [ make_int_varinfo "i";
      make_int_varinfo "x";
      make_int_varinfo "y";
      make_int_varinfo "z";
      make_int_array_varinfo "a";
      make_bool_varinfo "b"]
  in
  let e0 =
    _Q
      (vm#expr "b")
      (_b (vm#expr "x") Plus ((vm#vi "a") $ (vm#expr "i")))
      sk_zero
  in
  let expression =
    _Q
      (vm#expr "b")
      (_b e0 Plus ((vm#vi "a") $ (_b (vm#expr "i") Plus sk_one)))
      sk_zero
  in
  let (z3vars, varm) = create_vars_map vm#get_vs in
  let conv_expr = make_z3 z3vars expression in
  printf "Expression : %s@." (Expr.to_string conv_expr);
  (** Test simplify *)
  let simpl_e = simplify_z3 conv_expr in
  printf "Simplified expression : %s@." (Expr.to_string conv_expr);
  (** Test converting back *)
  let e_sk = from_expr varm simpl_e in
  printf "Expression : %a@." pp_skexpr e_sk
