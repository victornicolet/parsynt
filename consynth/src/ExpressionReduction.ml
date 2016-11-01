open Utils
open SketchTypes
open Cil
open SPretty
open Format
open Expressions

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
    | SkQuestion (_, _,_) -> true
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
    | SkQuestion (c, x, y)->
      let x' = rfunc x in let y' = rfunc y in
      let c = rfunc c in
      begin
        match x', y' with
        | SkBinop (op1, x1, x2), SkBinop (op2, y1, y2)
          when op1 = op2 && is_associative op1 ->
          let cx1 = cost stv c_exprs x1 in
          let cx2 = cost stv c_exprs x2 in
          let cy1 = cost stv c_exprs y1 in
          let cy2 = cost stv c_exprs y2 in
          if x1 = y1 && cx1 > (max cx2 cy2) then
            let cond = rfunc (SkQuestion (c, x2, y2)) in
            SkBinop (op1, x1, cond)
          else
            begin
              if x2 = y2 && cx2 > (max cx1 cy1) then
                let cond = rfunc (SkQuestion (c, x1, y1)) in
                SkBinop (op1, cond, x2)
              else
                SkQuestion (c, x', y')
            end
        | _, _ -> SkQuestion (c, x', y')
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
  let flat_r = (flatten_AC r0) in
  let r1 = apply_special_rules stv c_exprs flat_r in
  let r2 = rebuild_tree_AC stv c_exprs r1 in
  r2


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
