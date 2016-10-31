open Utils
open SketchTypes
open Cil
open SPretty
open Format
open Expressions

(** Compute the 'cost' of an expression with respect to a set of other
    c-expressions : the cost is the pair of the maximum depth of a
    c-expression in the expressions and the number of c-expressions in
    the expressions.
    @param stv the set of state variables.
    @param expr the expression of which we need to compute the cost.
    @return a pair of ints, the first element is the maximum depth of
    c-expression in the expression abstract syntax tree and the second element
    is the number of occurrences of c-expressions.
*)
let rec depth_cost (vs : VS.t) (c_exprs : ES.t) expr =
  let cost = expression_cost vs c_exprs expr in
  (cost.max_depth, cost.occurrences)

and depth_c_func vs c_exprs func =
  match func with
  | SkLetIn (velist, l') ->
    let dl', cl' = depth_c_func vs c_exprs l' in
    let max_de, sum_c =
      (List.fold_left
         (fun (mde, sec) (de, ec) -> (max mde de, sec + ec))
         (0, 0)
         (List.map (fun (v, e) -> depth_cost vs c_exprs e) velist)) in
    ((max max_de (if dl' > 0 then dl' + 1 else 0)), sum_c + cl')
  | SkLetExpr velist ->
    (List.fold_left
       (fun (mde, sec) (de, ec) -> (max mde de, sec + ec))
       (0, 0)
       (List.map (fun (v, e) -> depth_cost vs c_exprs e) velist))


let cost stv c_exprs expr =
  depth_cost stv c_exprs expr


(** op2 is right-distributive over op1 if :
    (a op1 b) op2 c = (a op2 c) op1 (b op2 c)
    @param op1 'sum' like operator
    @param op2 distributes over op1
    @return true if op2 is right distributive over op1
*)


(** Equality of expressions under commutativity *)
let reduce_cost stv c_exprs expr =
  let reduction_cases expr =
    match expr with
    | SkBinop (_, _, _) -> true
    | _ -> false
  in
  let reduce_transform rfunc expr =
    match expr with
    | SkBinop (op2, x, y) ->
      let x' = rfunc x in
      let y' = rfunc y in
      begin
        match x', y' with
        | SkBinop (op1, a, b), c ->
          let a' = rfunc a in
          let b' = rfunc b in
          let c' = c in
          let ca = cost stv c_exprs a' in
          let cb = cost stv c_exprs b' in
          let cc = cost stv c_exprs c' in
          (* [(a + b) * c --> a*c + b*c] if no stv in c *)
          if is_right_distributive op1 op2 && ((max ca cb) > cc)
          then
            SkBinop (op1, rfunc (SkBinop (op2, a', c')),
                     rfunc (SkBinop (op2, b', c')))
          else
            expr
        | _, _ -> SkBinop (op2, x', y')
      end
  | SkUnop (op, e) -> SkUnop(op, rfunc e)
  | e -> rfunc e
  in
  transform_expr reduction_cases reduce_transform identity identity expr



let reduce_full ?(limit = 10) stv c_exprs expr =
  let rec aux_apply_ternary_rules limit red_expr =
    let red_expr = reduce_cost stv c_exprs expr in
    if red_expr = expr || limit = 0
    then red_expr
    else aux_apply_ternary_rules (limit - 1) red_expr
  in
  let r0 = aux_apply_ternary_rules limit expr in
  let r1 = rebuild_tree_AC stv c_exprs (flatten_AC r0) in
  r1


(** Using Rosette to solve other reduction/expression matching problems *)
let find_function_with_rosette all_vars fe e =
  let pp_defs fmt () =
    Sketch.pp_symbolic_definitions_of fmt all_vars
  in
  let pp_expr_e fmt () =
    fprintf fmt "(define e @[%a@])@." pp_skexpr e
  in
  let pp_expr_fe fmt () =
    fprintf fmt "(define fe @[%a@])@." pp_skexpr fe
  in
  let pp_f_sketch fmt vars =
    fprintf fmt "(define (f x) (bExpr %s x 2))" vars
  in
  let pp_synth_prob fmt s () =
    fprintf fmt
      "(define odot (synthesize #:forall (list %s) \
       #:guarantee (assert (eq? fe (f e)))))@."
      s
  in
  let pp_all fmt () =
    let defs_str = String.concat " " (pp_defs fmt ()) in
    pp_expr_e fmt ();
    pp_expr_fe fmt ();
    pp_f_sketch fmt defs_str;
    pp_synth_prob fmt defs_str ()
  in
  let solution = Local.compile_and_fetch pp_all () in
  Ast.pp_expr_list Format.std_formatter solution
