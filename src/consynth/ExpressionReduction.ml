(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
  *)


open Beta
open Utils
open Fn
open Cil
open FnPretty
open Format
open Expressions


let verbose = ref true

let rec is_stv vset expr =
  match expr with
  | FnUnop (_, FnVar v)
  | FnVar v ->
    begin
      try
        VarSet.mem (check_option (vi_of v)) vset
      with Failure s -> false
    end
  | FnCond (c, e1, e2) -> is_stv vset c
  | _ -> false


let scalar_normal_form (vset : VarSet.t) (e : fnExpr) =
  let is_candidate =
    function
    | FnBinop (_, e1, e2)
    | FnCond (_, e1, e2) ->
      (** One of the operands must be a state variable
          but not the other *)
      (is_stv vset e1 && (not (fn_uses vset e2))) ||
      (is_stv vset e2 && (not (fn_uses vset e1)))
    (* Special rule for conditionals *)
    | _ ->  false
  in

  let handle_candidate f =
    function
    | FnBinop (_, e1, e2) ->
      begin
        match e1, e2 with
        | FnCond(c, _, _), estv when is_stv vset estv ->
          [1]
        | estv, FnCond(c, _, _) when is_stv vset estv ->
          [1]
        | e, estv  when is_stv vset estv -> [1]
        | estv, e when is_stv vset estv -> [1]
        | _ -> []
      end

    | FnCond (_, e1, e2) ->
      if is_stv vset e1 then
        [1]
      else
        [1]
    | _ ->  []
  in
  let collected = (rec_expr
                     (fun a b -> a@b)
                     []
                     is_candidate
                     handle_candidate
                     (fun c -> [])
                     (fun v -> [])
                     e)
  in
  (List.length collected) <= ((VarSet.cardinal vset) + 1)





let reduce_cost_binop rfunc ctx (op2 : symb_binop) (x : fnExpr) (y : fnExpr) =
  match x, y with
  (** Transform comparisons with max min into conjunctions
      or disjunctions, because conj/disj. are associative *)
  (* max(a, b) > c --> a > c or b > c *)
  | FnBinop (Max, a, b), c when op2 = Gt || op2 = Ge ->
    FnBinop (Or, FnBinop (op2, a, c), FnBinop (op2, b, c))
  (* c > max(a, b) --> c > a and c > b *)
  | c, FnBinop (Max, a, b) when op2 = Gt || op2 = Ge ->
    FnBinop (And, FnBinop (op2, c, a), FnBinop (op2, c, b))
  (* max(a, b) < c --> a < c and b < c *)
  | FnBinop (Max, a, b), c when op2 = Lt || op2 = Le ->
    FnBinop (And, FnBinop (op2, a, c), FnBinop (op2, b, c))
  (* c < max(a, b) --> c < a or c < b *)
  | c, FnBinop (Max, a, b) when op2 = Lt || op2 = Le ->
    FnBinop (Or, FnBinop (op2, c, a), FnBinop (op2, c, b))


  (* Distributivity with operators *)
  | FnBinop (op1, a, b), c ->
    let ca = cost ctx a in
    let cb = cost ctx b in
    let cc = cost ctx c in
    (* [(a + b) * c --> a*c + b*c] if no stv in c *)
    if is_right_distributive op1 op2 && ((max ca cb) >= cc)
    then
      FnBinop (op1, (FnBinop (op2, a, c)),
               (FnBinop (op2, b, c)))

    else
      FnBinop (op2, x, y)

  | c, FnBinop (Or, a , b) when op2 = And ->
    FnBinop (Or, FnBinop (And, c, a), FnBinop (And, c, b))

  (* Distributivity with ternary expressions *)
  | FnCond (cond, a, b), c ->
    let ca = cost ctx a in
    let cb = cost ctx b in
    let cc = cost ctx c in
    if is_associative op2 &&  (max ca cb) > cc then
      FnCond (cond, FnBinop (op2, a, c), FnBinop (op2, b, c))
    else
      FnBinop (op2, x, y)

  | c, FnCond (cond, a, b) ->
    let ca = cost ctx a in
    let cb = cost ctx b in
    let cc = cost ctx c in
    if is_associative op2 && (max ca cb) > cc then
      FnCond (cond, FnBinop (op2, c, a), FnBinop (op2, c, b))
    else
      FnBinop (op2, x, y)

  | _, _ -> FnBinop (op2, x, y)


let reduce_cost_ternary rfunc ctx c x y =
  match x, y with
  | FnBinop (op1, x1, x2), FnBinop (op2, y1, y2)
    when op1 = op2 && is_associative op1 ->
    let cx1 = cost ctx x1 in
    let cx2 = cost ctx x2 in
    let cy1 = cost ctx y1 in
    let cy2 = cost ctx y2 in
    if x1 = y1 && cx1 > (max cx2 cy2) then
      let cond = rfunc (FnCond (c, x2, y2)) in
      FnBinop (op1, x1, cond)
    else
      begin
        if x2 = y2 && cx2 > (max cx1 cy1) then
          let cond = rfunc (FnCond (c, x1, y1)) in
          FnBinop (op1, cond, x2)
        else
          FnCond (c, x, y)
      end
  | _, _ -> FnCond (c, x, y)



(**
   Reduce the cost of an expression. The cost is computed according to the ctx
   information, which contains 'costly' expressions.
 *)
let reduce_cost ctx expr =
  let reduction_cases expr =
    match expr with
    | FnBinop (_, _, _) -> true
    | FnCond (_, _,_) -> true
    | FnUnop (_,_) -> true
    | _ -> false
  in
  (* Tranform expressions by looking at its leaves *)
  let reduce_transform rfunc expr =
    match expr with
    | FnBinop (op2, x, y) ->
      reduce_cost_binop rfunc ctx op2 (rfunc x) (rfunc y)

    | FnCond (c, x, y)->
      reduce_cost_ternary rfunc ctx (rfunc c) (rfunc x) (rfunc y)

    (* Distribute unary boolean not down, unary num neg down *)
    | FnUnop (op, x) ->
      let e' = rfunc x in
      begin
      match op, e' with
      | Not, FnBinop (And, e1, e2) ->
        FnBinop(Or, rfunc (FnUnop (Not, e1)), rfunc (FnUnop (Not, e2)))

      | Not, FnBinop (Or, e1, e2) ->
        FnBinop(And, rfunc (FnUnop (Not, e1)), rfunc (FnUnop (Not, e2)))

      | Neg, FnBinop (Plus, e1, e2) ->
        FnBinop(Plus, rfunc (FnUnop (Neg, e1)), rfunc (FnUnop (Neg, e2)))

      | Neg, FnBinop (Minus, e1, e2) ->
        FnBinop(Minus, rfunc e1, rfunc e2)

      | _, _ -> FnUnop(op, e')
      end
      (* End FnUnop (op, e) case *)
    | _ -> failwith "Unexpected case in expression transformation"

  (* End transform expressions *)
  in
  transform_expr reduction_cases reduce_transform identity identity expr

let reduce_cost_specials ctx e=
  let red_cases e =
    match e with
    | FnCond _ -> true
    | _ -> false
  in
  let red_apply rfunc e =
    match e with
    | FnCond (cond1, x, y) ->
      let x' = rfunc x in
      let y' = rfunc y in
      begin
        match x', y' with
        | FnCond (cond2, a, b), c ->
          let ca = cost ctx a in
          let cb = cost ctx b in
          let cc = cost ctx c in
          if ca > (max cb cc) then
            FnCond (FnBinop (And, cond1, cond2), a,
                        FnCond (FnUnop (Not, cond2), c, b))
          else
            FnCond (cond1, x, y)
        | _ ->  FnCond (cond1, x, y)
      end
    | _ -> failwith "Unexpected case in reduce_cost_specials"
  in
  transform_expr red_cases red_apply identity identity e

let remove_double_negs ctx e=
  let red_cases e =
    match e with
    | FnUnop _ -> true
    | _ -> false
  in
  let red_apply_dbn rfunc e =
    match e with
    | FnUnop (op, e') ->
      let e'' = rfunc e' in
      begin
        match op, e'' with
        | Not, FnUnop (op2, e0) when op2 = Not -> rfunc e0
        | Neg, FnUnop (op2, e0) when op2 = Neg -> rfunc e0
        | _ , _ -> FnUnop(op, e'')
      end
    | _ -> failwith "Unexpected case in reduce_cost_specials"
  in
  transform_expr red_cases red_apply_dbn identity identity e


let force_linear_normal_form ctx e =
  let distr_for_linear op expr_list =
    let aux acc e =
      let e' = rebuild_tree_AC ctx e in
      match e' with
      | FnBinop(op1, e0, FnBinop(op2, u,v))
        when is_right_distributive op2 op1 &&
             op2 = op ->
        acc@[FnBinop(op1, e0, u);FnBinop(op1, e0, v)]

      | FnBinop(op1, FnBinop(op2, u,v), e0)
        when is_left_distributive op2 op1 &&
             op2 = op ->
        acc@[FnBinop(op1, u, e0);FnBinop(op1, v, e0)]

      | _ ->
        acc@[e]
    in
    List.fold_left aux [] expr_list
  in

  let factor_largest_common t top_op el =
    let flat_el = List.map flatten_AC el in
    let flat_ops, remainder =
      List.partition
        (fun e ->
           match e with
           | FnApp(t, Some opvar, _) ->
             is_some (op_from_name opvar.vname)
           | _ -> false)
        flat_el
    in
    let op_assoc =
      let add_op_elt op el opmap =
        try
          let elts = List.assoc op opmap in
          let opmap' = List.remove_assoc op opmap in
          (op, el::elts)::opmap'
        with Not_found ->
          (op, [el])::opmap
      in
      List.fold_left
        (fun opmap expr ->
           match expr with
           | FnApp(t, Some opvar, el) ->
             let op = check_option (op_from_name opvar.vname) in
             add_op_elt op el opmap
           | _ -> opmap)
        [] flat_ops
    in
    (List.fold_left
      (fun el (op,assoce) ->
         el@(find_max_state_factors ctx t top_op (get_AC_op op) assoce)) []
      op_assoc) @ remainder
  in
  (* Try to apply distributivity rules that can make the expression
     linear normal. *)
  let flat_e = flatten_AC e in
  let e_tree = match flat_e with
    | FnApp(t, Some opvar, el) ->
      begin
        match op_from_name opvar.vname with
        | Some op ->
          let el' = distr_for_linear op el in
          let el'' = factor_largest_common t opvar el' in
          rebuild_tree_AC ctx
            (FnApp(t, Some opvar, el''))
        | None -> e
      end
    | _ -> e
  in e_tree


let reduce_full ?(limit = 10) (ctx : context) (expr : fnExpr) =
  let rec aux_apply_ternary_rules ctx limit e =
    let red_expr0 = reduce_cost ctx e in
    let red_expr1 = reduce_cost_specials ctx red_expr0 in
    let red_expr = remove_double_negs ctx.state_vars red_expr1 in
    if red_expr @= e || limit = 0
    then red_expr
    else aux_apply_ternary_rules ctx (limit - 1) red_expr
  in
  let rules_AC e =
    let flat_r = (flatten_AC e) in
    let r1 = apply_special_rules ctx flat_r in
    rebuild_tree_AC ctx r1
  in
  let r0 = aux_apply_ternary_rules ctx limit expr in
  if scalar_normal_form ctx.state_vars r0 then
    rules_AC r0
  else
    (force_linear_normal_form ctx
       (factorize_multi_toplevel ctx r0))


let rec normalize ctx sklet =
  match sklet with
  | FnLetIn (ve_list, letin) ->
    FnLetIn (List.map (fun (v, e) -> (v, reduce_full ctx e)) ve_list,
             normalize ctx letin)
  | FnRecord(vs, emap) ->
    let ve_list = unwrap_state vs emap in
    wrap_state (List.map (fun (v, e) -> (v, reduce_full ctx e)) ve_list)

  | e -> reduce_full ctx e


let clean_unused_assignments : fnExpr -> fnExpr =
  let is_rec_mem e =
    match e with
    | FnRecordMember _ -> true
    | _ -> false
  in
  let rec remove_to_ignore ignore_list =
    transform_expr2
      {
        case = (fun e -> match e with FnLetIn _ -> true | _ -> false);
        on_case =
          (fun f e ->
             match e with
             | FnLetIn (bindings, cont) ->
               let rem_b =
                 List.filter
                   (fun (v,e) ->
                      not (List.mem v ignore_list) || is_rec_mem e)
                   bindings
               in
               let rec_b = (List.map (fun (v,e) -> (v, f e)) rem_b) in
               begin match rec_b with
               | [] -> f cont
               | _ -> FnLetIn(rec_b, f cont) end

             | _ -> failwith "x"
          );
        on_var = identity;
        on_const = identity;
      }
  in
  transform_expr2
    { case = (fun e -> match e with FnLetIn _ -> true | _ -> false);
      on_case = (fun f e ->
          match e with
          | FnLetIn([(v, FnRec(igu, st, (s, body)))], FnRecord(rvs, remap)) ->
            let choices = unwrap_state rvs remap in
            let to_ignore =
              List.fold_left
                (fun l (v,e) ->
                   match e with
                   | FnRecordMember _ -> l
                   | _ -> v :: l) [] choices
            in
            FnLetIn([(v, FnRec(igu, st, (s, remove_to_ignore to_ignore body)))],
                    wrap_state choices)
          | FnLetIn(b, cont) -> FnLetIn(b, f cont)
          | _ -> failwith "Guarded clause");
      on_var = identity;
      on_const = identity;
    }

let clean ctx e =
  clean_unused_assignments e

(** Using Rosette to solve other reduction/expression matching problems *)
let find_function_with_rosette all_vars fe e =
  let pp_defs fmt () =
    Sketch.pp_symbolic_definitions_of fmt [] all_vars
  in
  let pp_expr_e fmt () =
    fprintf fmt "(define e @[%a@])@." pp_fnexpr e
  in
  let pp_expr_fe fmt () =
    fprintf fmt "(define fe @[%a@])@." pp_fnexpr fe
  in
  let pp_f_sketch fmt () =
    fprintf fmt "(define (f x) (bExpr %a x 2))"
      Sketch.pp_defined_input all_vars
  in
  let pp_synth_prob fmt () =
    fprintf fmt
      "(define odot (synthesize #:forall (list %a) \
       #:guarantee (assert (eq? fe (f e)))))@."
      Sketch.pp_defined_input all_vars
  in
  let pp_all fmt () =
    pp_defs fmt ();
    pp_expr_e fmt ();
    pp_expr_fe fmt ();
    pp_f_sketch fmt ();
    pp_synth_prob fmt  ()
  in
  let _, solution = Local.compile_and_fetch Conf.rosette pp_all () in
  RAst.pp_expr_list Format.std_formatter solution
