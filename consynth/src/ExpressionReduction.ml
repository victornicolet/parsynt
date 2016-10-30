open Utils
open SketchTypes
open Cil
open SPretty
open Format

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
  match expr with
  | e when ES.mem expr c_exprs ->
    (1, 1)
  | SkVar v ->
     begin
      try
        let vi = check_option (vi_of v) in
        let is_stv = if VSOps.has_vid vi.vid vs then 1 else 0 in
        (is_stv, is_stv)
      with Failure s -> (0, 0)
    end
  | SkConst _ -> (0, 0)
  | SkCastE (_, e)
  | SkUnop (_, e)
  | SkSizeofE e
  | SkAlignofE e
  | SkStartOf e ->
    let de, ec = depth_cost vs c_exprs e in
    ((if de > 0 then de + 1 else de), ec)

  | SkBinop (_, e1, e2) ->
    let de1, ec1 = depth_cost vs c_exprs e1 in
    let de2, ec2 = depth_cost vs c_exprs e2 in
    let mde = max de1 de2 in
    ((if mde > 0 then mde + 1 else 0), ec1 + ec2)

  | SkQuestion (c, e1, e2) ->
    let dec, ecc = depth_cost vs c_exprs c in
    let de1, ec1 = depth_cost vs c_exprs e1 in
    let de2, ec2 = depth_cost vs c_exprs e2 in
    let mde = max (max de1 de2) dec in
    ((if mde > 0 then mde + 1 else 0), ecc + ec1+ ec2)

  | SkCond (c, l1, l2) ->
    let dec, ecc = depth_cost vs c_exprs c in
    let de1, ec1 = depth_c_func vs c_exprs l1 in
    let de2, ec2 = depth_c_func vs c_exprs l2 in
    let mde = max (max de1 de2) dec in
    ((if mde > 0 then mde + 1 else 0), ecc + ec1 + ec2)

  | _ -> (0,0)


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
  let dep, count = depth_cost stv c_exprs expr in
  dep

(** op2 is right-distributive over op1 if :
    (a op1 b) op2 c = (a op2 c) op1 (b op2 c)
    @param op1 'sum' like operator
    @param op2 distributes over op1
    @return true if op2 is right distributive over op1
*)
let is_right_distributive op1 op2 =
  (** (a op1 b) op2 c = (a op2 c) op1 (b op2 c) *)
  match op1, op2 with
  | Or, And
  | Min, Plus
  | Max, Plus
  | Plus, Times -> true
  | _, _ ->  false

let is_left_distributive op1 op2 =
  (**  a op2 (b op1 c) = (a op1 b) op2 (a op1 c) *)
  match op1, op2 with
  | Plus, Times
  | Or, And -> true
  | _ , _ -> false

let is_associative op =
  match op with
  | And | Or | Plus | Times | Max | Min -> true
  | _ -> false


(** Input is (a + b) + c *)
let associative_case_R op (a, ca) (b, cb) (c, cc) =
  (* (a + b) + c *)
  if ca > (max cb cc)
  then SkBinop (op, a, (SkBinop (op, b, c))) (* a + (b + c) *)
  else SkBinop (op, (SkBinop (op, a, b)), c) (* Unchanged *)


let associative_case_L op (a, ca) (b, cb) (c, cc) =
  (* a + (b + c) *)
  if cc > (max ca cb)
  then SkBinop (op, (SkBinop (op, a, b)), c)   (* (a + b) + c *)
  else SkBinop (op, a, (SkBinop (op, b, c))) (* Unchanged *)

let flatten_assoc vs es expr =
  let cost_fun = cost vs es in
  let rec get_expr_list assoc_op expr =
    match expr with
    | SkBinop (op, e1, e2) when op = assoc_op ->
      ((get_expr_list assoc_op e1)@(get_expr_list assoc_op e2))
    | _ -> [expr]
  in
  let rebuild_expr op topleft_e el =
    List.fold_right
      (fun elt acc -> SkBinop (op, elt, acc)) el topleft_e
  in
  let expr_list, maybe_op =
    match expr with
    | SkBinop (op, _, _) ->
      if is_associative op then
        get_expr_list op expr, Some op
      else [], None
    | _ -> [], None
  in
  if is_some maybe_op then
    let op = check_option maybe_op in
    (** Ordered in decreasing cost *)
    let ordered_list =
      List.rev
        (List.sort (fun e1 e2 -> compare (cost_fun e1) (cost_fun e2)) expr_list)
    in
    (** Should be longer than 1 since we're considering binary operators *)
    match ordered_list with
    | hd::tl when tl != [] -> Some (rebuild_expr op hd tl)
    | _ -> None
  else
    None


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
            begin
              (* [(a + b) + c -> a + (b + c)]  *)
              if (op1 = op2) && (is_associative op1)
              then
                associative_case_R op1 (a', ca) (b', cb) (c', cc)
              else
                expr
            end

        | a , SkBinop (op1, b, c) ->
          let a' = x' in
          let b' = rfunc b in
          let c' = rfunc c in
          let ca = cost stv c_exprs a' in
          let cb = cost stv c_exprs b' in
          let cc = cost stv c_exprs c' in
          begin
            (* [(a + b) + c -> a + (b + c)]  *)
            if (op1 = op2) && (is_associative op1)
            then
              associative_case_L op1 (a', ca) (b', cb) (c', cc)
            else
              expr
          end
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
  match flatten_assoc stv c_exprs r0 with
  | Some e -> r0
  | None -> r0

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
