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

open FuncTypes
open Utils
open FPretty
module IH = Sets.IH

let debug = ref false
let narrow_array_completions = ref false

let auxiliary_variables : fnV IH.t = IH.create 10

let cur_left_auxiliaries = ref VarSet.empty
let cur_right_auxiliaries = ref VarSet.empty

let left_aux_ids = ref []
let right_aux_ids = ref []

let add_laux_id i = left_aux_ids := i :: !left_aux_ids
let add_raux_id i = right_aux_ids := i :: !right_aux_ids

let is_left_aux i = List.mem i !left_aux_ids

let is_right_aux i = List.mem i !right_aux_ids

let init () =
  IH.clear auxiliary_variables;
  cur_left_auxiliaries := VarSet.empty;
  cur_right_auxiliaries := VarSet.empty

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

let rec make_holes ?(max_depth = 1) ?(is_final = false) ?(is_array = false)
    (index_expr : fnExpr)
    (state : VarSet.t)
    (optype : operator_type) =
  let holt t = (t, optype) in
  let self_rcall =
    make_holes ~max_depth:max_depth ~is_final:is_final ~is_array:is_array index_expr state
  in
  function
  | FnVar var ->
    begin
      match var with
      | FnVariable vi ->
        let t = vi.vtype in
        if (IH.mem auxiliary_variables vi.vid) && is_final
        then FnVar var, 0
        else
          (if VarSet.mem vi state
           then FnHoleL (holt t, var, CS.complete_all (CS.of_vs state), index_expr), 1
           else FnHoleR (holt t, CS.complete_right (CS.of_vs state), index_expr), 1)
      | FnArray (sklv, expr) ->
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
              FnHoleL (holt t, sklv, CS.complete_all completion, index_expr), 1
            else
              FnHoleR (holt t, CS.complete_right (CS.of_vs state), index_expr), 1)
         | _ -> failhere __FILE__ "make_holes" "Unexpected type in array")
      | FnTuple vs -> FnVar (FnTuple vs), 0
    end

  | FnConst c ->
    let cs = CS.complete_right (CS.of_vs state) in
    begin
      match c with
      | CInt _ | CInt64 _ -> FnHoleR (holt Integer, cs, index_expr), 1
      | CReal _ -> FnHoleR (holt Real, cs, index_expr), 1
      | CBool _ -> FnHoleR (holt Boolean, cs, index_expr), 1
      | _ -> FnHoleR (holt Unit, cs, index_expr), 1
    end

  | FnFun skl -> FnFun (make_join ~index:index_expr ~state:state ~skip:[] ~w_a:(ref false) skl), 0

  | FnBinop (op, e1, e2) ->
    let holes1, d1 = merge_leaves max_depth (self_rcall optype e1) in
    let holes2, d2 = merge_leaves max_depth (self_rcall optype e2) in
    FnBinop (op, holes1, holes2), max d1 d2

  | FnUnop (op, e) ->
    merge_leaves max_depth (self_rcall optype e)

  | FnCond (c, ei, ee) ->
    let h1, d1  = merge_leaves max_depth (self_rcall optype ei) in
    let h2, d2 = merge_leaves max_depth (self_rcall optype ee) in
    let hc, dc = merge_leaves max_depth (self_rcall optype c) in
    FnCond (hc, h1, h2), max (max d1 d2) dc

  | FnApp (t, vo, args) ->
    let new_args, depths =
      ListTools.unpair (List.map (self_rcall optype) args) in
    FnApp (t, vo, new_args), ListTools.intlist_max depths

  | _ as skexpr ->  skexpr, 0


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

and make_assignment_list ie state skip writes_in_array =
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
  List.map (fun (vbound, e) ->
      match e with
      | FnVar v when v = vbound && in_skip_list v skip -> (v, e)

      | FnApp (st, f, args) ->
        (vbound, e)

      | _ ->
        try
          let vi_bound = check_option (vi_of vbound) in
          if VarSet.mem vi_bound !cur_left_auxiliaries ||
             VarSet.mem vi_bound !cur_right_auxiliaries  then
            (vbound, FnHoleL (((type_of e), Basic), vbound,
                         CS.complete_all (CS.of_vs state), ie))
          else
            (match vi_bound.vtype with
             | Vector _ ->
               writes_in_array := true;
               (vbound, fst (make_hole_e ~is_array:true ~is_final:true ie state e))
             | _ ->
               (vbound, fst (make_hole_e ~is_final:true ie state e)))
        with Failure s ->
          Format.eprintf "Failure %s@." s;
          let msg =
            Format.sprintf "Check if %s is vi failed." (FPretty.sprintFnexpr e)
          in
          failhere __FILE__ "make_assignment_list"  msg
    )

and make_join ~(index : fnExpr) ~(state : VarSet.t) ~(skip: fnLVar list) ~(w_a: bool ref) =
  function
  | FnLetExpr ve_list ->
    FnLetExpr (make_assignment_list index state skip w_a ve_list)

  | FnLetIn (ve_list, cont) ->
    let to_skip = fst (ListTools.unpair ve_list) in
    FnLetIn (
      make_assignment_list index state skip w_a ve_list,
      make_join ~index:index ~state:state ~skip:(skip@to_skip) ~w_a:w_a cont)
  | e -> e

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

let set_types_and_varsets =
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

     identity identity)


(* TODO change the limits *)
let wrap_with_loop for_inner i state base_join =
  let start_state_val =
    if for_inner then
      let lsp =  VarSet.add_prefix state (Conf.get_conf_string "rosette_join_left_state_prefix")  in
      (FnLetExpr (identity_state lsp))
    else
      (fst (make_hole_e i state (FnLetExpr (identity_state state))))
  in
  FnRec ((FnConst (CInt 0),
          FnBinop (Lt, i, FnConst (CInt 10)),
          FnUnop (Add1,i)),
         (state, start_state_val),
         base_join)


let make_loop_wrapped_join ?(for_inner=false) outeri state fnlet =
  (* Get the base skeleton *)
  let writes_in_array = ref false in
  let base_join = make_join ~index:outeri ~state:state ~skip:[] ~w_a:writes_in_array fnlet in
  if !writes_in_array then
    wrap_with_loop for_inner outeri state base_join
  else
    base_join

let build i (state : VarSet.t) fnlet =
  set_types_and_varsets (make_loop_wrapped_join i state fnlet)

let build_for_inner i state fnlet =
  narrow_array_completions := true;
  let raw_sketch = make_loop_wrapped_join ~for_inner:true i state fnlet in
  let typed_sketch = set_types_and_varsets raw_sketch in
  narrow_array_completions := false;
  typed_sketch
