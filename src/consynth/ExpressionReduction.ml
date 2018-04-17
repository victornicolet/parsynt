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

open Utils
open FuncTypes
open Cil
open FPretty
open Format
open Expressions


let verbose = ref true

let reduce_cost_binop rfunc ctx (op2 : symb_binop) (x : fnExpr) (y : fnExpr) =
  match x, y with
  (** Transform comparisions with max min into conjunctions
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
  | FnQuestion (cond, a, b), c ->
    let ca = cost ctx a in
    let cb = cost ctx b in
    let cc = cost ctx c in
    if is_associative op2 &&  (max ca cb) > cc then
      FnQuestion (cond, FnBinop (op2, a, c), FnBinop (op2, b, c))
    else
      FnBinop (op2, x, y)

  | c, FnQuestion (cond, a, b) ->
    let ca = cost ctx a in
    let cb = cost ctx b in
    let cc = cost ctx c in
    if is_associative op2 && (max ca cb) > cc then
      FnQuestion (cond, FnBinop (op2, c, a), FnBinop (op2, c, b))
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
      let cond = rfunc (FnQuestion (c, x2, y2)) in
      FnBinop (op1, x1, cond)
    else
      begin
        if x2 = y2 && cx2 > (max cx1 cy1) then
          let cond = rfunc (FnQuestion (c, x1, y1)) in
          FnBinop (op1, cond, x2)
        else
          FnQuestion (c, x, y)
      end
  | _, _ -> FnQuestion (c, x, y)



(**
   Reduce the cost of an expression. The cost is computed according to the ctx
   information, which contains 'costly' expressions.
 *)
let reduce_cost ctx expr =
  let reduction_cases expr =
    match expr with
    | FnBinop (_, _, _) -> true
    | FnQuestion (_, _,_) -> true
    | FnUnop (_,_) -> true
    | _ -> false
  in
  (* Tranform expressions by looking at its leaves *)
  let reduce_transform rfunc expr =
    match expr with
    | FnBinop (op2, x, y) ->
      reduce_cost_binop rfunc ctx op2 (rfunc x) (rfunc y)

    | FnQuestion (c, x, y)->
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
    | FnQuestion _ -> true
    | _ -> false
  in
  let red_apply rfunc e =
    match e with
    | FnQuestion (cond1, x, y) ->
      let x' = rfunc x in
      let y' = rfunc y in
      begin
        match x', y' with
        | FnQuestion (cond2, a, b), c ->
          let ca = cost ctx a in
          let cb = cost ctx b in
          let cc = cost ctx c in
          if ca > (max cb cc) then
            FnQuestion (FnBinop (And, cond1, cond2), a,
                        FnQuestion (FnUnop (Not, cond2), c, b))
          else
            FnQuestion (cond1, x, y)
        | _ ->  FnQuestion (cond1, x, y)
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

let reduce_full ?(search_linear=false) ?(limit = 10) ctx expr =
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
  let r' =
    if search_linear then
      let r'' = aux_apply_ternary_rules {ctx with costly_exprs = ES.empty} limit expr in
      factorize_multi_toplevel ctx r''
    else
      expr
  in
  let r0 = aux_apply_ternary_rules ctx limit r' in
  let r2 = rules_AC r0 in
  r2

let rec normalize ctx sklet =
  match sklet with
  | FnLetIn (ve_list, letin) ->
    FnLetIn (List.map (fun (v, e) -> (v, reduce_full ctx e)) ve_list,
             normalize ctx letin)
  | FnLetExpr ve_list ->
    FnLetExpr (List.map (fun (v, e) -> (v, reduce_full ctx e)) ve_list)

  | e -> reduce_full ctx e


(** WIP: normalizing conditional paths.  *)


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
