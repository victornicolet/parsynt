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

let auxiliary_variables : fnV IH.t = IH.create 10

let cur_left_auxiliaries = ref VarSet.empty
let cur_right_auxiliaries = ref VarSet.empty

let left_aux_ids = ref []
let right_aux_ids = ref []

let add_laux_id i = left_aux_ids := i :: !left_aux_ids
let add_raux_id i = right_aux_ids := i :: !right_aux_ids

let is_left_aux i =
  List.mem i !left_aux_ids

let is_right_aux i =
  List.mem i !right_aux_ids

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
  | FnHoleR (t, cs) -> FnHoleR(t', cs)
  | FnHoleL (t, v, cs) -> FnHoleL(t', v, cs)
  | e -> e

let type_of_hole =
  function
  | FnHoleR (t, _) | FnHoleL (t, _, _) -> Some t
  | _ -> None

let completion_vars_of_hole =
  function
  | FnHoleR (_, cs) -> cs
  | FnHoleL (_, _, cs) -> cs
  | _ -> CS.empty

let rec make_holes ?(max_depth = 1) ?(is_final = false) (state : VarSet.t)
    (optype : operator_type) =
  let holt t = (t, optype) in
  function
  | FnVar sklv ->
    begin
      match sklv with
      | FnVariable vi ->
        let t = vi.vtype in
        if (IH.mem auxiliary_variables vi.vid) && is_final
        then FnVar sklv, 0
        else
          (if VarSet.mem vi state
           then FnHoleL (holt t, sklv, CS.complete_all (CS.of_vs state)), 1
           else FnHoleR (holt t, CS.complete_right (CS.of_vs state)), 1)
      | FnArray (sklv, expr) ->
        (** Array : for now, cannot be a stv *)
        let t = type_of_var sklv in
        (match t with
         | Vector (t, _) -> FnHoleR (holt t, CS.complete_right (CS.of_vs state)), 1
         | _ -> failhere __FILE__ "make_holes" "Unexpected type in array")
      | FnTuple vs -> FnVar (FnTuple vs), 0
    end

  | FnConst c ->
    let cs = CS.complete_right (CS.of_vs state) in
    begin
      match c with
      | CInt _ | CInt64 _ -> FnHoleR (holt Integer, cs), 1
      | CReal _ -> FnHoleR (holt Real, cs), 1
      | CBool _ -> FnHoleR (holt Boolean, cs), 1
      | _ -> FnHoleR (holt Unit, cs), 1
    end

  | FnFun skl -> FnFun (make_join ~state:state ~skip:[] skl), 0

  | FnBinop (op, e1, e2) ->
    let holes1, d1 = merge_leaves max_depth (make_holes state optype e1) in
    let holes2, d2 = merge_leaves max_depth (make_holes state optype e2) in
    FnBinop (op, holes1, holes2), max d1 d2

  | FnUnop (op, e) ->
    merge_leaves max_depth (make_holes state optype e)

  | FnCond (c, li, le) ->
    let ch, _ = make_holes state optype c in
    FnCond (ch ,
            make_join ~state:state ~skip:[] li,
            make_join ~state:state ~skip:[] le), 0

  | FnQuestion (c, ei, ee) ->
    let h1, d1  = merge_leaves max_depth (make_holes state optype ei) in
    let h2, d2 = merge_leaves max_depth (make_holes state optype ee) in
    let hc, dc = merge_leaves max_depth (make_holes state optype c) in
    FnQuestion (hc, h1, h2), max (max d1 d2) dc

  | FnApp (t, vo, args) ->
    let new_args, depths =
      ListTools.unpair (List.map (make_holes state optype) args) in
    FnApp (t, vo, new_args), ListTools.intlist_max depths

  | _ as skexpr ->  skexpr, 0


and make_hole_e
    ?(max_depth = 2)
    ?(is_final=false)
    (state : VarSet.t) (e : fnExpr) =
  let optype = analyze_optype e in
  make_holes
    ~max_depth:max_depth
    ~is_final:is_final
    state optype e

and make_assignment_list state skip =
  List.map (fun (v, e) ->
      match e with
      | FnVar v when List.mem v skip -> (v, e)

      | FnApp (st, f, args) ->
        (v, e)

      | _ ->
        try
          let vi = check_option (vi_of v) in
          if VarSet.mem vi !cur_left_auxiliaries ||
             VarSet.mem vi !cur_right_auxiliaries  then
            (v, FnHoleL (((type_of e), Basic), v,
                         CS.complete_all (CS.of_vs state)))
          else
            (v, fst (make_hole_e ~is_final:true state e))
        with Failure s ->
          Format.eprintf "Failure %s@." s;
          let msg =
            Format.sprintf "Check if %s is vi failed." (FPretty.sprintFnexpr e)
          in
          failhere __FILE__ "make_assignment_list"  msg
    )

and make_join ~(state : VarSet.t) ~(skip: fnLVar list) =
  function
  | FnLetExpr ve_list ->
    FnLetExpr (make_assignment_list state skip ve_list)

  | FnLetIn (ve_list, cont) ->
    let to_skip = fst (ListTools.unpair ve_list) in
    FnLetIn (
      make_assignment_list state skip ve_list,
      make_join ~state:state ~skip:(skip@to_skip) cont)
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
        (match (type_of_binop (res_type t1) (res_type t2) op) with
         | Some t ->
           if t1 = t2 && rh_h1 && rh_h2 then
             let ht_final = Function (t1, t) in
             FnHoleR ((ht_final, join_optypes o1 o2), vars), d
           else
             FnBinop(op, h1, h2), d + 1

         | None -> failwith "Type error in holes")

      | FnApp (t, ov, el) ->
        let all_holes, vars =
          List.fold_left
            (fun (is_h, vars) e ->
               (is_h && is_right_hole e,
                CS.union vars (completion_vars_of_hole e)))

            (true, CS.empty) el
        in
        if all_holes
        then
          FnHoleR ((t, NotNum), vars), d
        else
          let el', _ = ListTools.unpair
              (List.map (fun e_ -> merge_leaves max_depth (e_, d)) el)
          in FnApp (t, ov, el'), d

      | FnQuestion (c, ei, ee) ->
        begin
          if is_a_hole ei && is_a_hole ee && is_a_hole c then
            FnQuestion (FnHoleR ((Boolean, NotNum), completion_vars_of_hole c),
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
         | FnHoleL ((t, o), v, vs) ->
           let nvs, nt = adapt_vs_and_t vs t in
           FnHoleL ((nt, o), v, nvs)

         | FnHoleR ((t, o), vs) ->
           let nvs, nt = adapt_vs_and_t vs t in
           FnHoleR ((nt, o), nvs)

         | _ -> rfun e)

      identity identity)


let build (state : VarSet.t) fnlet =
  set_types_and_varsets (make_join ~state:state ~skip:[] fnlet)
