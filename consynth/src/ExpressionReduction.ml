open Utils
open SketchTypes
open Cil
open SPretty
open Format

(** Depth of state variables in the expression tree and number of occurrences
    in the expression tree.
    @param stv the set of state variables.
    @param expr the expression of which we need to compute the cost.
    @return a pair of ints, the first element is the maximum depth of state
    variables in the expression abstract syntax tree and the second element
    is the number of occurrences of state variables.
*)
let rec depth_cost stv expr =
  match expr with
  | SkVar v ->
    begin
      try
        let vi = check_option (vi_of v) in
        let is_stv = if VSOps.has_vid vi.vid stv then 1 else 0 in
        (is_stv, is_stv)
      with Failure s -> (0, 0)
    end
  | SkConst _ -> (0, 0)
  | SkCastE (_, e)
  | SkUnop (_, e)
  | SkSizeofE e
  | SkAlignofE e
  | SkStartOf e ->
    let de, ec = depth_cost stv e in
    ((if de > 0 then de + 1 else de), ec)

  | SkBinop (_, e1, e2) ->
    let de1, ec1 = depth_cost stv e1 in
    let de2, ec2 = depth_cost stv e2 in
    let mde = max de1 de2 in
    ((if mde > 0 then mde + 1 else 0), ec1 + ec2)

  | SkQuestion (c, e1, e2) ->
    let dec, ecc = depth_cost stv c in
    let de1, ec1 = depth_cost stv e1 in
    let de2, ec2 = depth_cost stv e2 in
    let mde = max (max de1 de2) dec in
    ((if mde > 0 then mde + 1 else 0), ecc + ec1+ ec2)

  | SkCond (c, l1, l2) ->
    let dec, ecc = depth_cost stv c in
    let de1, ec1 = depth_c_func stv l1 in
    let de2, ec2 = depth_c_func stv l2 in
    let mde = max (max de1 de2) dec in
    ((if mde > 0 then mde + 1 else 0), ecc + ec1 + ec2)

  | _ -> (0,0)


and depth_c_func stv func =
  match func with
  | SkLetIn (velist, l') ->
    let dl', cl' = depth_c_func stv l' in
    let max_de, sum_c =
      (List.fold_left
         (fun (mde, sec) (de, ec) -> (max mde de, sec + ec))
         (0, 0)
         (List.map (fun (v, e) -> depth_cost stv e) velist)) in
    ((max max_de (if dl' > 0 then dl' + 1 else 0)), sum_c + cl')
  | SkLetExpr velist ->
    (List.fold_left
       (fun (mde, sec) (de, ec) -> (max mde de, sec + ec))
       (0, 0)
       (List.map (fun (v, e) -> depth_cost stv e) velist))



let cost stv expr =
  let dep, count = depth_cost stv expr in
  dep

(** op2 is right-distributive over op1 if :
    (a op1 b) op2 c = (a op2 c) op1 (b op2 c)
    @param op1 'sum' like operator
    @param op2 distributes over op1
    @return true if op2 is right distributive over op1
*)
let is_right_distributive op1 op2 =
  match op1, op2 with
  | Or, And
  | Min, Plus
  | Max, Plus
  | Plus, Times -> true
  | _, _ ->  false

let is_associative op =
  match op with
  | And | Or | Plus | Times | Max | Min -> true
  | _ -> false


let reduce_cost stv expr =
  let reduction_cases expr =
    match expr with
    | SkBinop (_, _, _) -> true
    | _ -> false
  in
  let reduce_transform rfunc expr =
    match expr with
  | SkBinop (op2, SkBinop (op1, a, b), c) ->
    let a' = rfunc a in
    let b' = rfunc b in
    let c' = rfunc c in
    if is_right_distributive op1 op2
    && ((max (cost stv a') (cost stv b')) >= (cost stv c'))
    then
      SkBinop (op1, rfunc (SkBinop (op2, a', c')), rfunc (SkBinop (op2, b', c')))
    else
      begin
        if (op1 = op2) && (is_associative op1)  &&
           ((cost stv a') >= (max (cost stv b') (cost stv c')))
        then
           (SkBinop (op2, a', SkBinop (op1, b', c')))
        else
          expr
      end
  | SkBinop (op, a, b) ->
    SkBinop (op, rfunc a, rfunc b)
  | SkUnop (op, e) -> SkUnop(op, rfunc e)
  | e -> rfunc e
  in
  transform_expr
    reduction_cases reduce_transform
    identity identity expr



let rec reduce_full ?(limit = 100) stv expr =
  let red_expr = reduce_cost stv expr in
  if red_expr = expr || limit = 0
  then red_expr
  else reduce_full ~limit:(limit - 1) stv red_expr

(** Using Rosette to solve other reduction/expression matching problems *)
let find_function all_vars fe e =
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
