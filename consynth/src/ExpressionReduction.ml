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
  (* Tranform expressions by looking at its leaves *)
  let reduce_transform rfunc expr =
    match expr with
    | SkBinop (op2, x, y) ->
      let x' = rfunc x in
      let y' = rfunc y in
      begin
        match x', y' with
        (** Transform comparisions with max min into conjunctions
            or disjunctions, because conj/disj. are associative *)
        (* max(a, b) > c --> a > c or b > c *)
        | SkBinop (Max, a, b), c when op2 = Gt || op2 = Ge ->
          SkBinop (Or, SkBinop (op2, a, c), SkBinop (op2, b, c))
        (* c > max(a, b) --> c > a and c > b *)
        | c, SkBinop (Max, a, b) when op2 = Gt || op2 = Ge ->
          SkBinop (And, SkBinop (op2, c, a), SkBinop (op2, c, b))
        (* max(a, b) < c --> a < c and b < c *)
        | SkBinop (Max, a, b), c when op2 = Lt || op2 = Le ->
          SkBinop (And, SkBinop (op2, a, c), SkBinop (op2, b, c))
        (* c < max(a, b) --> c < a or c < b *)
        | c, SkBinop (Max, a, b) when op2 = Lt || op2 = Le ->
          SkBinop (Or, SkBinop (op2, c, a), SkBinop (op2, c, b))


        (* Distributivity with operators *)
        | SkBinop (op1, a, b), c ->
          let ca = cost stv c_exprs a in
          let cb = cost stv c_exprs b in
          let cc = cost stv c_exprs c in
          (* [(a + b) * c --> a*c + b*c] if no stv in c *)
          if is_right_distributive op1 op2 && ((max ca cb) >= cc)
          then
            SkBinop (op1, (SkBinop (op2, a, c)),
                     (SkBinop (op2, b, c)))

          else
            SkBinop (op2, x', y')
        (* Distributivity with ternary expressions *)
        | SkQuestion (cond, a, b), c ->
          let ca = cost stv c_exprs a in
          let cb = cost stv c_exprs b in
          let cc = cost stv c_exprs c in
          if is_associative op2 &&  (max ca cb) > cc then
            SkQuestion (cond, SkBinop (op2, a, c), SkBinop (op2, b, c))
          else
            SkBinop (op2, x', y')

        | c, SkQuestion (cond, a, b) ->
          let ca = cost stv c_exprs a in
          let cb = cost stv c_exprs b in
          let cc = cost stv c_exprs c in
          if is_associative op2 && (max ca cb) > cc then
            SkQuestion (cond, SkBinop (op2, c, a), SkBinop (op2, c, b))
          else
            SkBinop (op2, x', y')

        | _, _ -> SkBinop (op2, x', y')
      end (* End SkBinop (c, x, y) case *)

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
      end (* End SkQuestion (c, x, y) case *)
    | _ -> failwith "Unexpected case in expression transformation"

  (* End transform expressions *)
  in
  transform_expr reduction_cases reduce_transform identity identity expr

let reduce_cost_specials stv c_exprs e=
  let red_cases e =
    match e with
    | SkQuestion _ -> true
    | _ -> false
  in
  let red_apply rfunc e =
    match e with
    | SkQuestion (cond1, x, y) ->
      let x' = rfunc x in
      let y' = rfunc y in
      begin
        match x', y' with
        | SkQuestion (cond2, a, b), c ->
          let ca = cost stv c_exprs a in
          let cb = cost stv c_exprs b in
          let cc = cost stv c_exprs c in
          if ca > (max cb cc) then
            SkQuestion (SkBinop (And, cond1, cond2), a,
                        SkQuestion (SkUnop (Not, cond2), c, b))
          else
            SkQuestion (cond1, x, y)
        | _ ->  SkQuestion (cond1, x, y)
      end
    | _ -> failwith "Unexpected case in reduce_cost_specials"
  in
  transform_expr red_cases red_apply identity identity e

let reduce_full ?(limit = 10) stv c_exprs expr =
  let rec aux_apply_ternary_rules limit e =
    let red_expr0 = reduce_cost stv c_exprs e in
    let red_expr = reduce_cost_specials stv c_exprs red_expr0 in
    if red_expr @= e || limit = 0
    then red_expr
    else aux_apply_ternary_rules (limit - 1) red_expr
  in
  let rules_AC e =
    let flat_r = (flatten_AC e) in
    let r1 = apply_special_rules stv c_exprs flat_r in
    rebuild_tree_AC stv c_exprs r1
  in
  let r0 = aux_apply_ternary_rules limit expr in
  let r2 = rules_AC r0 in
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
