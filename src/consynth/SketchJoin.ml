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
open Fn
open Utils
open FnPretty
open Format
module IH = Sets.IH
module E = Expressions

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
    if !verbose then
      printf "@.[INFO] Store inner join solution %s.@."
        (Conf.join_name sol.loop_name);
    SH.add _inner_joins (Conf.join_name sol.loop_name)
      (sol.scontext, sol.memless_solution)

  | None -> ()

let store_ctx_sol name o =
  SH.add _inner_joins name o


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
  | FnHoleR (t, cs, i, d) -> FnHoleR(t', cs, i, d)
  | FnHoleL (t, v, cs, i, d) -> FnHoleL(t', v, cs, i, d)
  | e -> e

let type_of_hole =
  function
  | FnHoleR (t, _, _, _) | FnHoleL (t, _, _, _, _) -> Some t
  | _ -> None

let completion_vars_of_hole =
  function
  | FnHoleR (_, cs, _, _) -> cs
  | FnHoleL (_, _, cs, _, _) -> cs
  | _ -> CS.empty

let midx_of_hole =
  function
  | FnHoleR (_, _,i, _) -> i
  | FnHoleL (_, _,_,i, _) -> i
  | _ -> FnConst(CNil)


(* Some transformations need to be wrapped in a recursive function *)
let force_wrap = ref false

let rec make_holes
    ?(max_depth = 1)
    ?(is_final = false)
    ?(is_array = false)
    ?(skip=[])
    (index_expr : fnExpr)
    (state : VarSet.t)
    (optype : operator_type)
    (expression : fnExpr) : fnExpr * int =
  let holt t = (t, optype) in
  let self_rcall =
    make_holes
      ~max_depth:max_depth ~is_final:is_final ~is_array:is_array  ~skip:skip
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
                                                   index_expr,
                                                   1))
                            emap) rvs IM.empty), 1
          | _ -> FnVar var, 0
        else
          (if VarSet.mem vi state
           then
             FnHoleL (holt t, var, CS._LorR (CS.of_vs state), index_expr, 1), 1
           else
             FnHoleR (holt t, CS._R (CS.of_vs state), index_expr, 1), 1)
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
                   CS._LorR completion, index_expr, 1),
          1
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
                                                   index_expr, 1))
                            emap) rvs IM.empty), 1
          | _ ->
            FnVar var,
            0
        else
          FnHoleR (holt t, CS._R (CS.of_vs state), index_expr, 1), 1)

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
      | CInt _ | CInt64 _ -> FnHoleR (holt Integer, cs, index_expr, 1), 1
      | CReal _ -> FnHoleR (holt Real, cs, index_expr, 1), 1
      | CBool _ -> FnHoleR (holt Boolean, cs, index_expr, 1), 1
      | _ -> FnHoleR (holt Unit, cs, index_expr, 1), 1
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
      make_assignment_list
        ~index_e:index_expr ~state:state ~skip:skip ~wa:w_a bindings
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

and make_assignment_list
    ~index_e:ie ~state:state ~skip:skip ~wa:writes_in_array =
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
  let add_assignments l (vbound,e) =
    match e with
    | FnVar v when v = vbound && in_skip_list v skip -> l @ [v, e]

    | FnConst c -> l @ [vbound, e]

    | FnApp (st, f, args) ->
      begin match f with
        | Some func ->
          (* Is it the join function of an inner loop? *)
          begin if Conf.is_inner_join_name func.vname then
              (if !verbose then printf "[INFO] Inline inner join in sketch.@.";
               let new_binds =
                 inline_inner_join ie state skip writes_in_array
                   (vbound, st, func, args)
               in
               (l @ new_binds))
            else
              l @ [(vbound, e)]
          end
        | None ->
          l @ [(vbound, e)]
      end

    | _ ->
      begin
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
                                  CS._LorR (CS.of_vs state), ie, 1)]
          else
            begin match vi_bound.vtype with
              | Vector _ ->
                writes_in_array := true;
                l @ [vbound, fst (make_hole_e ~is_array:true ie state e)]
              | _ ->
                l @ [vbound, fst (make_hole_e ie state e)]
            end
        with Failure s ->
          Format.eprintf "[ERROR] Failure %s@." s;
          let msg =
            Format.sprintf "Check if %s is vi failed." (FnPretty.sprintFnexpr e)
          in
          failhere __FILE__ "make_assignment_list"  msg
      end
  in
  List.fold_left add_assignments []



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
      if all_are_record_member record_assignments then
        Some record_assignments, body
      else
        None, fexpr
    | _ -> None, fexpr
  in

  let rec drill body =
    let drill_bindings bindings =
              List.map
          (fun (v, e) ->
             match e with
               | FnVar v' when v = v' ->
                 (v,e)
               | _ ->
                 (v, fst(make_hole_e ~max_depth:1 ~is_array:!wa index state e)))
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

  let m _s igu vs bs sarg b : (fnLVar * fnExpr) list =
    wa := state_has_array;
    if !optim_use_raw_inner then
      [vbound, FnRec (igu, (vs, bs), (sarg, b))]
    else
      let maybe_ra, core_body = strip_record_assignments b in
      (match maybe_ra with
       | Some ra ->
         let core_body' = drill core_body in
         let to_inline =
           [vbound, FnRec(igu, (vs,bs), (sarg, FnLetIn(ra, core_body')))]
         in
         if !verbose then
           printf "@[<v 4>[INFO] INLINE THIS: %a@]@." pp_fnexpr
             (FnRec(igu, (vs,bs), (sarg, FnLetIn(ra, core_body'))));
         to_inline

       | None ->
         failhere __FILE__ "inline_inner_join"
           "Missing bindings in inner join loop body.")
  in
  match get_inner_solution f.vname with
  | Some (ctx, func) ->
    begin
      match func with
      (* Match shape of solution of inner join.*)
      | FnLetIn([(_s, FnRec (igu, (vs, bs), (sarg, b)))], _) ->
        m _s igu vs bs sarg b

      | FnLetIn(scs, FnLetIn([(_s, FnRec (igu, (vs, bs), (sarg, b)))], _)) ->
        let core = m _s igu vs bs sarg b in core

      | _ -> failhere __FILE__ "inline_inner_join"
               "Toplevel form of inner join not recognized."
    end
  | None ->
    failhere __FILE__ "inline_inner_join" ("Cannot find inner join "^f.vname)



and make_join ~(index : fnExpr) ~(state : VarSet.t) ~(skip: fnLVar list)
    ~(w_a: bool ref) body =
  let rec make_assignments local_skip e =
    match e with
    | FnRecord (vs, emap) ->
      [make_assignment_list index state local_skip w_a (unwrap_state vs emap)]

    | FnLetIn (ve_list, cont) ->
      let to_skip = fst (ListTools.unpair ve_list) in
      make_assignment_list index state skip w_a ve_list ::
      make_assignments (local_skip@to_skip) cont

    | _ ->
      failhere __FILE__ "make_join"
        "make_join called on non-binding expression."
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
    wrap_state
      ((make_assignments [] --> List.flatten --> remap_bindings_to_state) body)
  else
    let bds = List.rev (make_assignments [] body) in
    match bds with
    | hd :: (rhd :: rtl) ->
      List.fold_left
        (fun cont binds -> FnLetIn(binds, cont)) (wrap_state hd) (rhd :: rtl)
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
             FnHoleR ((ht_final, join_optypes o1 o2), vars, idx, 1), d
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
          FnHoleR ((t, NotNum), vars, idx, 1), d
        else
          let el', _ = ListTools.unpair
              (List.map (fun e_ -> merge_leaves max_depth (e_, d)) el)
          in FnApp (t, ov, el'), d

      | FnCond (c, ei, ee) ->
        begin
          if is_a_hole ei && is_a_hole ee && is_a_hole c then
            FnCond (
              FnHoleR (
                (Boolean, NotNum),
                completion_vars_of_hole c,
                midx_of_hole ee,
                1),
              ei,
              ee),
            d
          else
            e, 0
        end
      (** Do not propagate expression depth into control statements*)
      | _ -> (e, 0)
    end
  else
    (e, d + 1)


let set_types_and_varsets (e : fnExpr) : fnExpr =
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
  transform_expr
    (fun e -> is_a_hole e)
    (fun rfun e ->
       match e with
       | FnHoleL ((t, o), v, vs, i, d) ->
         let nvs, nt = adapt_vs_and_t vs t in
         FnHoleL ((nt, o), v, nvs, i, d)

       | FnHoleR ((t, o), vs, i, d) ->
         let nvs, nt = adapt_vs_and_t vs t in
         FnHoleR ((nt, o), nvs, i, d)

       | _ -> rfun e)

    identity identity e


(* Sketch size can be reduced for memoryless join *)
let rec inner_optims (state : VarSet.t) (letfun : fnExpr) : fnExpr  =
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
             | FnHoleL(_, v, _, _, _) -> FnVar v
             | FnHoleR _ -> e
             | _ -> e);
        on_const = identity;
        on_var = identity;
      }
      expr
  in
  match letfun with
  | FnRec (igu, s, (_s, body)) ->
    FnRec (igu, s, (_s, loop_inner_optims body))
  | FnLetIn ([s, innerb], cont) ->
    FnLetIn([s, inner_optims state innerb], cont)
  | e -> e


(* Refine completions.
   - Don't use arrays with cell ref outside loops. *)
let refine_completions (letfun : fnExpr) : fnExpr =
  let in_loops vs =
    let filter_out_outervs =
      CS.filter (fun cse -> VarSet.mem cse.cvi vs)
    in
    transform_expr2
      {
        case =
          (fun e ->
            match e with FnHoleR _ | FnHoleL _ -> true | _ -> false);
        on_case =
          (fun f e -> match e with
             | FnHoleR (t, cs, e, d) ->
               FnHoleR (t, CS._LRorRec (filter_out_outervs cs), e, d)
             | FnHoleL (t, v, cs, e, d) ->
               FnHoleL (t, v, CS._LRorRec (filter_out_outervs cs), e, d)
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
    | FnHoleL (t, v, cs, e, d) ->
      FnHoleL (t, v, filter_out_arrays cs, e, d)
    | FnHoleR (t, cs, e, d) ->
      FnHoleR (t, filter_out_arrays cs, e, d)
    | FnRec (igu, (vs,bs), (s, e)) ->
      FnRec(igu, (vs,bs), (s, in_loops vs e))
    | _ -> e
  in
  transform_expr2
    {case = case; on_case = on_case; on_const = identity; on_var = identity}
    letfun


let wrap_with_loop
    (i : fnExpr)
    (bounds : fnExpr * fnExpr)
    (state : VarSet.t)
    (reach_consts : fnExpr IM.t)
    (base_join : fnExpr) : fnExpr =
  let i_start, i_end = bounds in
  let start_state_valuation =
    let lsp =
      VarSet.add_prefix state
        (Conf.get_conf_string "rosette_join_left_state_prefix")
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
  let state_binder = special_binder (record_type state) in
  FnRec ((i_start,
          FnBinop (Lt, i, i_end),
          FnUnop (Add1,i)),
         (state, start_state_valuation),
         (state_binder, FnLetIn (bind_state state_binder state, base_join)))


(**
   Add a choice after the join to enable 'dropping' variables. Can be useful
   when the join  is a loop and one of the variables's join function is more
   naturally expressed as a constant time function rather than a function of a
   list. Avoids problems especially when the variable is always initialized at
   the beginning of the loop body, could be used as a temporary variable in the
   join loop, but its final value is only the value of the right or the top
   chunk.
*)
let wrap_with_choice (state : VarSet.t) (base_join : fnExpr) : fnExpr =
  let binder = mkFnVar "loop_res" (record_type state) in
  let rprefix = (Conf.get_conf_string "rosette_join_right_state_prefix") in
  let final_choices =
    List.map
      (fun v ->
         let rightval = {v with vname = rprefix ^ v.vname} in
         (mkVar v, FnChoice(
             [FnRecordMember(mkVarExpr binder, v.vname);
              mkVarExpr rightval])))
      (VarSet.elements state)
  in
  FnLetIn([(FnVariable binder, base_join)],
          wrap_state final_choices)


let make_loop_join i bounds state fnlet =
  let lsp  =
    VarSet.add_prefix state
      (Conf.get_conf_string "rosette_join_left_state_prefix")
  in
  let state_vars_to_left_thread =
    transform_expr (fun e -> false) (fun f e -> e)
      (fun c -> c)
      (fun v ->
         if VarSet.mem (var_of_fnvar v) state then
           begin match v with
             | FnVariable var ->
               FnVariable (VarSet.find_by_id lsp var.vid )
             | FnArray(FnVariable var, ie) ->
               FnArray (FnVariable
                          (VarSet.find_by_id lsp var.vid), ie)
             | _ -> failwith "not supported."
           end
         else v)
  in
  let _wa = ref true in
  let idx (i,g,u) =
    try
      mkVarExpr (VarSet.max_elt
                   (VarSet.inter (used_in_fnexpr g) (used_in_fnexpr u)))
    with Not_found ->
      failhere __FILE__ "make_loop_join" "Loop to drill has no index."
  in
  let drill_loop_body (i,g,u) (vs, bs) (s, lbody) =
    let idx = idx (i,g,u) in
    let ist, iend = bounds in
    let nbs =
      match bs with
      | FnRecord(vs, emap) ->
        let nemap = IM.map state_vars_to_left_thread emap in
        FnRecord(vs, nemap)
      | _ -> failwith "not expected."
    in
    let loop_join_body =
      make_join ~index:idx ~state:state ~skip:[] ~w_a:_wa lbody
    in
    FnRec((ist, FnBinop(Lt, idx, iend), FnUnop(Add1, idx)),
                        (vs, nbs),
                        (s, to_rec_completions loop_join_body))
  in
  let final_expr (vs, expr) =
    let linvar =
      List.map (fun var -> FnVariable var)
        (VarSet.elements
           (VarSet.filter (fun var -> is_array_type var.vtype) vs))
    in
    make_join ~index:(FnConst (CInt 0)) ~state:state
      ~skip:linvar ~w_a:_wa expr
  in
  match fnlet with
  | FnLetIn([v, FnRec((init,g,u), (vs,bs),(s, lbody))], expr) ->
    (* If the last `expr` after the loop updates a variable
       that depends on array variables,
       through another variable for example, *)
    let push_in_loop, idmap =
      let ctxt =
        let x = mk_ctx (used_in_fnexpr expr) state in
        {x with index_vars = used_in_fnexpr (idx (i,g,u))}
      in
      (* Variables of the state that depend on a linear variable through
         linear dependencies.
      *)
      let vars_w_deps_lin =
        let i_dlin =
          IM.filter
            (fun k vs -> VarSet.exists (fun var -> is_array_type var.vtype) vs)
            (FnDep.collect_dependencies ctxt fnlet)
        in
        List.map
          (fun (k, _) -> VarSet.find_by_id state k)
          (IM.to_alist i_dlin)
      in
      let x = VarSet.diff (VarSet.of_list vars_w_deps_lin) vs in
      x,
      VarSet.fold (fun var m -> IM.add var.vid (mkVarExpr var) m) x IM.empty
    in
    (* Extend the loop body with the variable depending on the linear state
       variables.
    *)
    if VarSet.cardinal push_in_loop > 0 then
      begin
        let vs', bs', s', lbody', expr' =
          let index = idx (i,g,u) in
          let ext_state = VarSet.union vs push_in_loop in
          let ext_bs =
            match bs with
            | FnRecord(vs, emap) ->
              FnRecord(ext_state, IM.add_all emap idmap)
            | _ ->
              failhere __FILE__ "make_loop_join" "Failed extending inner loop."
          in
          let s' = mkFnVar "s" (record_type ext_state) in
          let ext_body =
            let lbody' =
              replace_expression (mkVarExpr s) (mkVarExpr s') lbody
            in
            let unwrap_added_vars =
              VarSet.fold
                (fun var bn -> (TestUtils._self s' var)::bn) ext_state []
            in
            let addmap =
              let lb =
                make_join ~index:index ~state:ext_state ~skip:[] ~w_a:_wa expr
              in
              last_expr push_in_loop lb
            in
            FnLetIn(unwrap_added_vars,
                    extend_final_state push_in_loop addmap lbody')
          in
          ext_state, ext_bs, s', ext_body, expr
        in
        FnLetIn([v, drill_loop_body (init,g,u) (vs', bs') (s', lbody')],
                final_expr (vs, expr))
      end
    else
      FnLetIn([v, drill_loop_body (init,g,u) (vs, bs) (s, lbody)],
              final_expr (vs, expr))

  | _ ->
    make_join ~index:i ~state:state ~skip:[] ~w_a:_wa fnlet




let add_drop_choice = ref true


let make_wrapped_join
    ?(for_inner=false)
    (outeri : fnExpr)
    (bounds : fnExpr * fnExpr)
    (state : VarSet.t)
    (reach_consts : fnExpr IM.t)
    (fnlet : fnExpr) : fnExpr =
  force_wrap := false;
  let writes_in_array = ref false in
  if has_loop fnlet then
    make_loop_join outeri bounds state fnlet
  else
    let base_join =
      make_join ~index:outeri ~state:state ~skip:[] ~w_a:writes_in_array fnlet
    in
    let wrapped_join =
      if (!writes_in_array || !force_wrap) && for_inner then
        let loop_join =
          wrap_with_loop outeri bounds state reach_consts
            (to_rec_completions base_join)
        in
        if !add_drop_choice then
          wrap_with_choice state loop_join
        else
          loop_join
      else
        base_join
    in
    refine_completions wrapped_join



let build_join
    ~inner:is_inner
    (ind_l : fnExpr list)
    (state : VarSet.t)
    (reach_consts : fnExpr IM.t)
    (bounds : fnExpr * fnExpr)
    (fnlet : fnExpr) : fnExpr =
  if is_inner then
    begin
      let i =
        match ind_l with
        | [i] -> i
        | [] -> FnConst (CInt 0)
        | _ ->
          failhere __FILE__ "build_for_inner"
            "Multiple inner loops not implemented."
      in
      narrow_array_completions := true;
      let raw_sketch =
        make_wrapped_join ~for_inner:true i bounds state reach_consts fnlet
      in
      let typed_sketch = set_types_and_varsets raw_sketch in
      let sketch = inner_optims state typed_sketch in
      narrow_array_completions := false;
      sketch
    end

  else
    begin match ind_l with
      | [] ->
        set_types_and_varsets
          (make_wrapped_join (FnConst (CInt 0)) bounds state IM.empty fnlet)
      | [i] ->
        set_types_and_varsets (make_wrapped_join i bounds state IM.empty fnlet)
      | _ ->
        failhere __FILE__ "build_join" "Multiple inner loops not implemented."
    end


let sketch_join problem =
  let inner_indexes =
    List.map (fun pb -> mkVarExpr (VarSet.max_elt pb.scontext.index_vars))
      problem.inner_functions
  in
  Dimensions.set_default ();
  {
    problem with
    join_sketch =
         complete_final_state problem.scontext.state_vars
           (build_join ~inner:false
              inner_indexes
              problem.scontext.state_vars
              problem.reaching_consts
              (Dimensions.bounds true problem)
              problem.main_loop_body)
  }




let sketch_inner_join problem =
  Dimensions.set_default ();
  let index_set = get_index_varset problem in
  {
    problem with
    memless_sketch =
      complete_final_state problem.scontext.state_vars
        (build_join ~inner:true
           (List.map mkVarExpr (VarSet.elements index_set))
           problem.scontext.state_vars
           problem.reaching_consts
           (Dimensions.bounds false problem)
           problem.main_loop_body)
  }



let match_hole_to_completion
    (sketch : fnExpr) (solution : fnExpr) : fnExpr option =
  if !verbose then
    printf "@[<v 4>[INFO] Sketch:@;%a@;Solution:@;%a@]@."
      pp_fnexpr sketch pp_fnexpr solution;

  let rec match_binding (v, e) (v', e') =
    match v, v' with
    | FnArray(av, ie), FnVariable var' ->
      (v', mhc (FnArraySet(FnVar av, ie, e)) e')
    | _, _ -> (v, mhc e e')

  and mhc h c =
    match h, c with
    | FnHoleL _, e
    | FnHoleR _, e
    | FnChoice _, e ->
      if !verbose then
        printf "@.[INFO] Hole solution: %a = %a.@."
          pp_fnexpr h pp_fnexpr (E.peval c);
      E.peval e

    | FnArraySet(ae, ie, e), FnArraySet(ae', ie', e') ->
      FnArraySet(mhc ae ae', mhc ie ie', mhc e e')

    | FnBinop(op, e1, e2), FnBinop(op', e1', e2') when op = op' ->
      FnBinop(op, mhc e1 e1', mhc e2 e2')

    | FnUnop(op, e), FnUnop(op', e') when op = op' ->
      FnUnop(op, mhc e e')

    | FnCond(c, t, f), FnCond(c', t', f') ->
      FnCond(mhc c c', mhc t t', mhc f f')

    | FnRec((i,g,u),(vs,bs),(s, body)),
      FnRec((i',g',u'),(vs', bs'),(s', body')) ->
      FnRec((mhc i i', mhc g g', mhc u u'), (vs', bs'), (s', mhc body body'))

    | FnLetIn (bindings, cont), FnLetIn (bindings', cont') ->
      FnLetIn (List.map2 match_binding bindings bindings',
               mhc cont cont')
    | FnRecord(vs, emap), FnRecord(vs', emap') ->
      FnRecord(vs, IM.of_alist (List.map2 (fun (i,e) (i',e') -> (i, mhc e e'))
                                  (IM.to_alist emap) (IM.to_alist emap')))
    | e, e' when e = e' -> e

    | _ ->
      if !verbose then
        begin
          printf "[INFO]%s ==== Solution and sketch do not match. ====%s@."
            (PpTools.color "red") PpTools.color_default;
          printf "       @[<v 4>%a@;!=@;%a@]@." pp_fnexpr h pp_fnexpr c;
        end;
      failwith "Mistmatch."
  in
  try
    Some (E.peval (mhc sketch solution))
  with _ ->
    None
