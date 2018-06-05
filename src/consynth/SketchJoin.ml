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
open FuncTypes
open Utils
open FPretty
open Format
module IH = Sets.IH


let verbose = ref false
let debug = ref false
let narrow_array_completions = ref false
let make_flat_join = ref false


let optim_use_raw_inner = ref false
(**
   Solutions of inner loops are stored for inlining.
*)
let _inner_joins : (context * fnExpr) SH.t = SH.create 10

let store_solution (maybe_solution : prob_rep option) : unit =
  match maybe_solution with

  | Some sol ->
    (* Check that the solution is not empty *)
    let solution_expr = sol.memless_solution in
    if solution_expr = FnRecord(VarSet.empty, IM.empty) then
      eprintf "[WARNING] Store empty solution? Loop: %s@." sol.loop_name;
    SH.add _inner_joins (Conf.join_name sol.loop_name) (sol.scontext, sol.memless_solution)

  | None -> ()

let get_inner_solution (join_name : string) : (context * fnExpr) option =
  try
    let (ctx, sol) = SH.find _inner_joins join_name in
    if sol = FnRecord(VarSet.empty, IM.empty) then None else Some (ctx, sol)
  with Not_found ->
    None



(* Returns true is the expression is a hole. The second
   boolean in the pair is useful when we are trying to merge
   holes. Any merge involving a left hole yields a left hole,
   and we can have a right holes if and only if all holes merged
   are right holes. *)
let is_a_hole =
  function
  | FnHoleL _ -> true
  | FnHoleR _ -> true
  | _ -> false

let is_right_hole =
  function
  | FnHoleR _ -> true
  | _ -> false

let replace_hole_type t' =
  function
  | FnHoleR (t, cs, i) -> FnHoleR(t', cs, i)
  | FnHoleL (t, v, cs, i) -> FnHoleL(t', v, cs, i)
  | e -> e

let type_of_hole =
  function
  | FnHoleR (t, _, _) | FnHoleL (t, _, _, _) -> Some t
  | _ -> None

let completion_vars_of_hole =
  function
  | FnHoleR (_, cs, _) -> cs
  | FnHoleL (_, _, cs, _) -> cs
  | _ -> CS.empty

let midx_of_hole =
  function
  | FnHoleR (_, _,i) -> i
  | FnHoleL (_, _,_,i) -> i
  | _ -> FnConst(CNil)


(* Some transformations need to be wrapped in a recursive function *)
let force_wrap = ref false

let rec make_holes ?(max_depth = 1) ?(is_final = false) ?(is_array = false) ?(skip=[])
    (index_expr : fnExpr)
    (state : VarSet.t)
    (optype : operator_type)
    expression =
  let holt t = (t, optype) in
  let self_rcall =
    make_holes ~max_depth:max_depth ~is_final:is_final ~is_array:is_array  ~skip:skip
      index_expr state
  in
  let make_hole_variable var vi =
    let t = vi.vtype in
        if (is_currently_aux vi) && is_final
        then FnVar var, 0
        else if is_record_type t then
          (* At this point, a variable of record type (not a record expression!)
             should be the summarized input from the inner loop. *)
          match t with
          | Record (s, lt) ->
            let stl, rvs = get_struct s in
            FnRecord(rvs,
                     VarSet.fold
                       (fun var emap ->
                          IM.add var.vid (FnHoleR (holt var.vtype,
                                   CS._R (CS.of_vs state),
                                   index_expr)) emap) rvs IM.empty), 1
          | _ -> FnVar var, 0
        else
          (if VarSet.mem vi state
           then
             FnHoleL (holt t, var, CS._LorR (CS.of_vs state), index_expr), 1
           else
             FnHoleR (holt t, CS._R (CS.of_vs state), index_expr), 1)
  in
  let make_hole_array var sklv expr =
    (match type_of_var sklv with
     | Vector (t, _) ->
       let vi = check_option (vi_of sklv) in
       (if VarSet.mem vi state
        then
          let completion =
            if is_array then
              CS.of_vs
                (VarSet.filter (fun v -> is_array_type v.vtype) state)
            else
              CS.of_vs state
          in
          FnHoleL (holt t,
                   FnArray(sklv, expr),
                   CS._LorR completion, index_expr),
          1
        else if is_record_type t then
          (* At this point, a variable of record type (not a record expression!) should
             be the summarized input from the inner loop. *)
          match t with
          | Record (s, lt) ->
            let stl, rvs = get_struct s in
            FnRecord(rvs,
                     VarSet.fold
                       (fun var emap ->
                          IM.add var.vid (FnHoleR (holt var.vtype,
                                                   CS._R (CS.of_vs state),
                                                   index_expr)) emap) rvs IM.empty), 1
          | _ ->
            FnVar var,
            0
        else
          FnHoleR (holt t, CS._R (CS.of_vs state), index_expr), 1)

     | _ -> failhere __FILE__ "make_holes" "Unexpected type in array")
  in
  match expression with
  | FnVar var ->
    (match var with
      | FnVariable vi ->
        make_hole_variable var vi

      | FnArray (sklv, expr) ->
        make_hole_array var sklv expr)


  | FnConst c ->
    let cs = CS._R (CS.of_vs state) in
    begin
      match c with
      | CInt _ | CInt64 _ -> FnHoleR (holt Integer, cs, index_expr), 1
      | CReal _ -> FnHoleR (holt Real, cs, index_expr), 1
      | CBool _ -> FnHoleR (holt Boolean, cs, index_expr), 1
      | _ -> FnHoleR (holt Unit, cs, index_expr), 1
    end


  | FnRecord(vs, emap) ->
    let new_members, depths =
      IM.fold
        (fun k (e, d) (emap', dlist) -> (IM.add k e emap', d::dlist))
        (IM.map (self_rcall optype) emap)
        (IM.empty, [])
    in
    FnRecord (vs, new_members), ListTools.intlist_max depths


  | FnFun skl ->
    FnFun (
      make_join ~index:index_expr ~state:state ~skip:[] ~w_a:(ref false) skl),
    0


  | FnBinop (op, e1, e2) ->
    let holes1, d1 = merge_leaves max_depth (self_rcall optype e1) in
    let holes2, d2 = merge_leaves max_depth (self_rcall optype e2) in
    FnBinop (op, holes1, holes2),
    max d1 d2


  | FnUnop (op, e) ->
    merge_leaves max_depth (self_rcall optype e)


  | FnCond (c, ei, ee) ->
    let h1, d1  = merge_leaves max_depth (self_rcall optype ei) in
    let h2, d2 = merge_leaves max_depth (self_rcall optype ee) in
    let hc, dc = merge_leaves max_depth (self_rcall optype c) in
    FnCond (hc, h1, h2), max (max d1 d2) dc


  | FnApp (t, vo, args) ->
    let new_args, depths =
      ListTools.unpair (List.map (self_rcall optype) args)
    in
    FnApp (t, vo, new_args), ListTools.intlist_max depths

  | FnArraySet(a, i, e) ->
    let e', d = self_rcall optype e in
    FnArraySet(a, i, e'), d

  | FnRecordMember _ -> expression, 0

  | FnLetIn (bindings, cont) ->
    let w_a = ref false in
    let new_bindings  =
      make_assignment_list ~index_e:index_expr ~state:state ~skip:skip ~wa:w_a bindings
    in
    let to_skip = fst (ListTools.unpair bindings) in
    let new_cont, _ =
      make_holes
        ~max_depth:max_depth
        ~is_final:is_final
        ~is_array:is_array
        ~skip:(skip@to_skip)
        index_expr state
        optype cont
    in
    FnLetIn (new_bindings, new_cont), 0

  | _ -> expression, 0




and make_hole_e ?(max_depth = 2) ?(is_array=false) ?(is_final=false)
    (index_expr : fnExpr) (state : VarSet.t) (e : fnExpr) =
  let optype = analyze_optype e in
  make_holes
    ~max_depth:(if is_array then max_depth else 1)
    ~is_final:is_final
    ~is_array:is_array
    index_expr
    (if !narrow_array_completions && is_array then
       (VarSet.filter (fun v -> is_array_type v.vtype) state)
     else
       state)
     optype e

and make_assignment_list ~index_e:ie ~state:state ~skip:skip ~wa:writes_in_array =
  let in_skip_list var skip =
    match var with
    | FnVariable v ->
      (match v.vtype with
      | Vector _ ->
        List.exists
          (fun skip_v -> match vi_of skip_v with
             | Some skip_fnv -> v = skip_fnv
             | None -> false) skip
      | _ -> List.mem var skip)

    | _ -> List.mem var skip
  in
  List.fold_left
    (fun l (vbound, e) ->
      match e with
      | FnVar v when v = vbound && in_skip_list v skip -> l @ [v, e]

      | FnConst c -> l @ [vbound, e]

      | FnApp (st, f, args) ->
        (match f with
        | Some func ->
          (* Is it the join function of an inner loop? *)
          (if Conf.is_inner_join_name func.vname then
             (if !verbose then printf "[INFO] Inline inner join in sketch.@.";
             let new_binds =
               inline_inner_join ie state skip writes_in_array (vbound, st, func, args)
             in
             (l @ new_binds))
           else
             l @ [(vbound, e)])
        | None ->
          l @ [(vbound, e)])

      | _ ->
        if !verbose && false then
          begin
          printf "[INFO] Hole in expr : %a@." pp_fnexpr e;
          printf "       Type : %a@." pp_typ (type_of e);
          printf "       Result: %a@."
            pp_fnexpr (let e, _ = (make_hole_e ie state e) in  e);
          end;
        try
          let vi_bound = check_option (vi_of vbound) in
          if is_left_aux vi_bound || is_right_aux vi_bound  then
            l @ [vbound, FnHoleL (((type_of e), Basic), vbound,
                         CS._LorR (CS.of_vs state), ie)]
          else
            (match vi_bound.vtype with
             | Vector _ ->
               writes_in_array := true;
               l @ [vbound, fst (make_hole_e ~is_array:true ie state e)]
             | _ ->
               l @ [vbound, fst (make_hole_e ie state e)])
        with Failure s ->
          Format.eprintf "[ERROR] Failure %s@." s;
          let msg =
            Format.sprintf "Check if %s is vi failed." (FPretty.sprintFnexpr e)
          in
          failhere __FILE__ "make_assignment_list"  msg
    ) []



and inline_inner_join
    (index : fnExpr)
    (state : VarSet.t)
    (skip : fnLVar list)
    (wa : bool ref)
    (vbound, st, f, args) : (fnLVar * fnExpr) list =
  let strip_record_assignments fexpr =
    let all_are_record_member =
      let pred (v, e) =
        match (v, e) with
        | FnVariable vi, FnRecordMember(_, s) -> vi.vname = s
        | _ -> false
      in
      List.for_all pred
    in
    match fexpr with
    | FnLetIn (record_assignments, body) ->
      if all_are_record_member record_assignments then Some record_assignments, body else None, fexpr
    | _ -> None, fexpr
  in

  let rec drill body =
    let drill_bindings bindings =
              List.map
          (fun (v, e) ->
             match e with
             | FnVar v' when v = v' -> (v,e)
             | _ -> (v, fst (make_hole_e ~max_depth:1 ~is_array:!wa index state e)))
          bindings
    in
    match body with
    | FnLetIn (b0, body') ->
      FnLetIn(drill_bindings b0, drill body')

    | FnRecord(vs, emap) -> wrap_state (drill_bindings (unwrap_state vs emap))

    | _ ->
      failhere __FILE__ "extract in inline_inner_join"
        "Expected bindings, got another expression."
  in


  let state_has_array =
    match st with
    | Record (name, slt) -> List.exists (fun (s,t) -> is_array_type t) slt
    | Vector _ -> true
    | _ -> false
  in

  wa := state_has_array;
  match get_inner_solution f.vname with
  | Some (ctx, func) ->
    begin
      match func with
      (* Match shape of solution of inner join.*)
      | FnLetIn([(_s, FnRec (igu, (vs, bs), (sarg, b)))], _) ->
        if !optim_use_raw_inner then
          [vbound, FnRec (igu, (vs, bs), (sarg, b))]
        else
          let maybe_ra, core_body = strip_record_assignments b in
          (match maybe_ra with
          | Some ra ->
            let core_body' = drill core_body in
            [vbound, FnRec(igu, (vs,bs), (sarg, FnLetIn(ra, core_body')))]
          | None ->
             failhere __FILE__ "inline_inner_join" "Missing bindings in inner join loop body.")

      | _ -> failhere __FILE__ "inline_inner_join" "Toplevel form of inner join not recognized."
    end
  | None ->
    failhere __FILE__ "inline_inner_join" "Cannot find inner join."



and make_join ~(index : fnExpr) ~(state : VarSet.t) ~(skip: fnLVar list) ~(w_a: bool ref) body =
  let rec make_assignments local_skip e =
    match e with
    | FnRecord (vs, emap) ->
      [make_assignment_list index state local_skip w_a (unwrap_state vs emap)]

    | FnLetIn (ve_list, cont) ->
      let to_skip = fst (ListTools.unpair ve_list) in
      make_assignment_list index state skip w_a ve_list ::
      make_assignments (local_skip@to_skip) cont

    | _ ->
      failhere __FILE__ "make_join" "make_join called on non-binding expression."
  in
  let remap_bindings_to_state bindings =
    let mapped_bindings =
      List.fold_left
        (fun remap (v,e) ->
           let var = var_of_fnvar v in
           if VarSet.mem var state then
             match v with
             | FnVariable x ->
               IM.add var.vid e remap
             | FnArray (a, j) ->
               IM.add var.vid (FnArraySet (FnVar a, j, e)) remap
           else
             raise Not_found)
      IM.empty
      bindings
    in
    List.map
      (fun v ->
         try
           (mkVar v, IM.find v.vid mapped_bindings)
         with Not_found ->
           (mkVar v, mkVarExpr v))
      (VarSet.elements state)
  in
  if !make_flat_join then
    wrap_state ((make_assignments [] --> List.flatten --> remap_bindings_to_state) body)
  else
    let bds = List.rev (make_assignments [] body) in
    match bds with
    | hd :: (rhd :: rtl) ->
      List.fold_left (fun cont binds -> FnLetIn(binds, cont)) (wrap_state hd) (rhd :: rtl)
    | [l] -> wrap_state l
    | _ -> wrap_state []



and merge_leaves max_depth (e,d) =
  if d + 1 >= max_depth then
    begin
      match e with
      | FnUnop (op , h) when is_a_hole h ->
        let ht, ot = check_option (type_of_hole h) in
        let op_type =
          (match type_of_unop ht op with
           | Some t -> t
           | None -> failwith "Type error in holes")
        in
        let ht_final =
          if op_type = ht then op_type else Function (ht, op_type)
        in
        replace_hole_type (ht_final, ot) h, d


      | FnBinop (op, h1, h2) when is_a_hole h1 && is_a_hole h2 ->
        let t1, o1 = check_option (type_of_hole h1) in
        let t2, o2 = check_option (type_of_hole h2) in
        let rh_h1 = is_right_hole h1 in
        let rh_h2 = is_right_hole h2 in
        let vars = CS.union (completion_vars_of_hole h1)
            (completion_vars_of_hole h2)
        in
        let idx = midx_of_hole h1
        in
        (match (type_of_binop (res_type t1) (res_type t2) op) with
         | Some t ->
           if t1 = t2 && rh_h1 && rh_h2 then
             let ht_final = Function (t1, t) in
             FnHoleR ((ht_final, join_optypes o1 o2), vars, idx), d
           else
             FnBinop(op, h1, h2), d + 1

         | None -> failwith "Type error in holes")

      | FnApp (t, ov, el) ->
        let all_holes, vars, idx =
          List.fold_left
            (fun (is_h, vars, idx) e ->
               (is_h && is_right_hole e,
                CS.union vars (completion_vars_of_hole e),
                midx_of_hole e))

            (true, CS.empty, FnConst(CNil)) el
        in
        if all_holes
        then
          FnHoleR ((t, NotNum), vars, idx), d
        else
          let el', _ = ListTools.unpair
              (List.map (fun e_ -> merge_leaves max_depth (e_, d)) el)
          in FnApp (t, ov, el'), d

      | FnCond (c, ei, ee) ->
        begin
          if is_a_hole ei && is_a_hole ee && is_a_hole c then
            FnCond (FnHoleR ((Boolean, NotNum), completion_vars_of_hole c, midx_of_hole ee),
                    ei, ee), d
          else
            e, 0
        end
      (** Do not propagate expression depth into control statements*)
      | _ -> (e, 0)
    end
  else
    (e, d + 1)

let set_types_and_varsets e =
  let adapt_vs_and_t cs t =
    let nvs = filter_cs_by_type (input_type_or_type t) cs in
    if CS.cardinal nvs = 0 then
      match t with
      | Function (it, rt) ->
        let nvs' = filter_cs_by_type rt cs in
        nvs', rt
      | _ -> nvs, t
    else
      nvs, t
  in
  (fun (i,j) ->
     (transform_expr
        (fun e -> is_a_hole e)
        (fun rfun e ->
           match e with
           | FnHoleL ((t, o), v, vs, i) ->
             let nvs, nt = adapt_vs_and_t vs t in
             FnHoleL ((nt, o), v, nvs, i)

           | FnHoleR ((t, o), vs, i) ->
             let nvs, nt = adapt_vs_and_t vs t in
             FnHoleR ((nt, o), nvs, i)

           | _ -> rfun e)

        identity identity (e (i, j))))


(* Sketch size can be reduced for memoryless join *)
let rec inner_optims state letfun  =
  let ctx_handle = ref (FnVariable (VarSet.max_elt state))  in
  let loop_inner_optims expr =
    transform_bindings
      {
        ctx = ctx_handle;
        case =
          (fun e ->
             match e with
             | FnHoleL _ | FnHoleR _ -> true
             | _ -> false);
        on_case =
          (fun f e ->
             match e with
             | FnHoleL(_, v, _, _) -> FnVar v
             | FnHoleR _ -> e
             | _ -> e);
        on_const = identity;
        on_var = identity;
      }
      expr
  in
  (fun bounds ->
     match letfun bounds with
     | FnRec (igu, s, (_s, body)) ->
       FnRec (igu, s, (_s, loop_inner_optims body))
     | FnLetIn ([s, innerb], cont) ->
       FnLetIn([s, inner_optims state (fun b -> innerb) bounds], cont)
     | e -> e)


(* Refine completions.
   - Don't use arrays with cell ref outside loops. *)
let refine_completions letfun =
  let in_loops vs =
    let filter_out_outervs =
      CS.filter (fun cse -> VarSet.mem cse.cvi vs)
    in
    transform_expr2
      {
        case = (fun e -> match e with FnHoleR _ | FnHoleL _ -> true | _ -> false);
        on_case =
          (fun f e -> match e with
             | FnHoleR (t, cs, e) ->
               FnHoleR (t, CS._LRorRec (filter_out_outervs cs), e)
             | FnHoleL (t, v, cs, e) ->
               FnHoleL (t, v, CS._LRorRec (filter_out_outervs cs), e)
             | _ -> e);
        on_var = identity;
        on_const = identity;
      }
  in
  let filter_out_arrays cs =
    CS.filter (fun cse -> not (is_array_type cse.cvi.vtype)) cs
  in
  let case e =
    match e with
    | FnHoleL _ -> true
    | FnHoleR _ -> true
    | FnRec _ -> true
    | _ -> false
  in
  let on_case f e =
    match e with
    | FnHoleL (t, v, cs, e) ->
      FnHoleL (t, v, filter_out_arrays cs, e)
    | FnHoleR (t, cs, e) ->
      FnHoleR (t, filter_out_arrays cs, e)
    | FnRec (igu, (vs,bs), (s, e)) ->
      FnRec(igu, (vs,bs), (s, in_loops vs e))
    | _ -> e
  in
  transform_expr2
    {case = case; on_case = on_case; on_const = identity; on_var = identity}
    letfun


let wrap_with_loop i state reach_consts base_join =
  let start_state_valuation =
    let lsp =
      VarSet.add_prefix state (Conf.get_conf_string "rosette_join_left_state_prefix")
    in
    let stv_or_cst =
      List.map
        (fun v ->
           (mkVar v,
            if IM.mem v.vid reach_consts then
              IM.find v.vid reach_consts
            else
              mkVarExpr v)) (VarSet.elements lsp)
    in
    (wrap_state stv_or_cst)
  in
  let state_binder = mkFnVar "__s" (record_type state) in
  (fun (i_start, i_end) ->
     FnRec ((i_start,
             FnBinop (Lt, i, i_end),
             FnUnop (Add1,i)),
            (state, start_state_valuation),
            (state_binder, FnLetIn (bind_state state_binder state, base_join))))


(**
   Add a choice after the join to enable 'dropping' variables. Can be useful when the join
   is a loop and one of the variables's join function is more naturally expressed as a
   constant time function rather than a function of a list.
   Avoids problems especially when the variable is always initialized at the beginning of
   the loop body, could be used as a temporary variable in the join loop, but its final value
   is only the value of the right or the top chunk.
*)
let wrap_with_choice state base_join =
  let special_state_var = mkFnVar (state_var_name state "_fs_") (record_type state) in
  let rprefix = (Conf.get_conf_string "rosette_join_right_state_prefix") in
  let structname = record_name state in
  let final_choices =
    List.map
      (fun v ->
         let accessor = record_accessor structname v in
         let rightval = {v with vname = rprefix ^ v.vname} in
         (mkVar v, FnChoice(
           [FnApp(v.vtype, Some accessor, [mkVarExpr special_state_var]);
            mkVarExpr rightval])))
      (VarSet.elements state)
  in
  (fun (i, j) ->
     FnLetIn([(mkVar special_state_var, base_join (i,j))], wrap_state final_choices))


let add_drop_choice = ref true


let make_loop_wrapped_join ?(for_inner=false) outeri state reach_consts fnlet =
  force_wrap := false;
  let writes_in_array = ref false in
  let base_join = make_join ~index:outeri ~state:state ~skip:[] ~w_a:writes_in_array fnlet in
  let wrapped_join =
    if (!writes_in_array || !force_wrap) && for_inner then
      let loop_join =
        wrap_with_loop outeri state reach_consts
          (to_rec_completions base_join)
      in
      if !add_drop_choice then
        wrap_with_choice state loop_join
      else
        loop_join
    else
      (fun (i,j) -> base_join)
  in
  (fun (i,j) -> refine_completions (wrapped_join (i,j)))

let build_join i (state : VarSet.t) fnlet =
  match i with
  | [] ->
    set_types_and_varsets (make_loop_wrapped_join (FnConst (CInt 0)) state IM.empty fnlet)
  | [i] ->
    set_types_and_varsets (make_loop_wrapped_join i state IM.empty fnlet)
  | _ ->
    failhere __FILE__ "build_join" "Multiple inner loops not implemented."


let build_for_inner il state reach_consts fnlet =
  let i =
    match il with
    | [i] -> i
    | [] -> FnConst (CInt 0)
    | _ ->
      failhere __FILE__ "build_for_inner" "Multiple inner loops not implemented."
  in
  narrow_array_completions := true;
    let raw_sketch = make_loop_wrapped_join ~for_inner:true i state reach_consts fnlet in
    let typed_sketch = set_types_and_varsets raw_sketch in
    let sketch = inner_optims state typed_sketch in
    narrow_array_completions := false;
    sketch


let rec partial_complete_sketch sketch solution =
  let arrange sk_b sol_b =
    List.map2
      (fun (sk_v, sk_e) (sk_v, sol_e) ->
         (sk_v, sk_e)) sk_b sol_b
  in
  match (sketch, solution) with
  | FnLetIn(sk_b, sk_f) , FnLetIn(sol_b, sol_f) ->
    FnLetIn (arrange sk_b sol_b, partial_complete_sketch sk_f sol_f)

  | FnRecord (sk_vs, sk_b), FnRecord (sol_vs, sol_b) ->
    FnRecord (sk_vs, sk_b)

  | _ -> sketch

let build_from_solution_inner il state reach_consts (solution, fnlet) =
  let sketch = build_for_inner il state reach_consts fnlet in
  (fun (i,j) -> partial_complete_sketch (sketch (i,j)) solution)
