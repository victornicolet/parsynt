(**
   This file is part of Parsynt.

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

let verbose = ref false

let restrict_func (variables : VarSet.t) (func : fnExpr) : fnExpr =
  let update_rectype name stl =
    let stl' =
      List.filter
        (fun (s,t) ->
           try
             let v = VarSet.find_by_name variables s in
             t = v.vtype
           with Not_found -> false) stl
    in
    let name' =
      let vs' =
        VarSet.filter
          (fun var ->
             List.exists (fun (s,t) -> s = var.vname && t = var.vtype) stl')
          variables
      in
      record_name vs'
    in
    Record(name', stl')
  in
  let cases e =
    match e with
    | FnLetIn _ | FnRec _ | FnRecord _ -> true
    | _ -> false
  in
  let restrict_bindings f bds =
    List.map
      (fun (v,e) -> (v, f e))
      (List.filter
         (fun (v,e) ->
            let var = var_of_fnvar v in
            match var.vtype with
            | Record(name, stl) -> true
            | _ -> VarSet.mem (var_of_fnvar v) variables) bds)
  in
  let restrict_var v =
    match v with
    | FnVariable var ->
      begin
        match var.vtype with
        | Record (name, stl) ->
          FnVariable {var with vtype = update_rectype name stl}
        | _ -> v
      end
    | _ -> v
  in
  let restrict_body f e =
    match e with
    | FnLetIn (bindings, expr) ->
      begin match restrict_bindings f bindings with
        | [] -> f expr
        | l -> FnLetIn(l, f expr)
      end

    | FnRecord(vs, emap) ->
      let nvs = VarSet.inter variables vs in
      FnRecord(nvs,
               IM.map f (IM.filter (fun k e -> VarSet.has_vid nvs k) emap))

    | FnRec ((i,g,u),(vs,bs),(s,body)) ->
      let nvs = VarSet.inter variables vs in
      let s' = {s with vtype = record_type nvs} in
      let bs' = f bs in
      let body' =
        f (replace_expression (mkVarExpr s) (mkVarExpr s') body)
      in
      FnRec ((i,g,u),(nvs,bs'),(s', body'))

    | _ -> e
  in
  transform_expr2
    {
      case = cases;
      on_case = restrict_body;
      on_var = restrict_var;
      on_const = identity
    }
    func


let restrict (problem : prob_rep) (variables : VarSet.t) : prob_rep =
  let new_body = restrict_func variables problem.main_loop_body in
  SketchJoin.sketch_inner_join
    (SketchJoin.sketch_join
       {
         problem with
         scontext = ctx_inter problem.scontext variables;
         main_loop_body = new_body;
         loop_body_versions = SH.create 5;
       })


let collect_dependencies (vars : VarSet.t) (func : fnExpr) : VarSet.t IM.t =
  let join_depmap a b =
    IM.fold
      (fun k be map' ->
         if IM.mem k map' then map' else
           IM.add k be map')
      b
      (IM.fold
         (fun k ae map' ->
            try
              IM.add k (VarSet.union ae (IM.find k b)) map'
            with Not_found ->
              IM.add k ae map') a IM.empty)
  in
  let case e =
    match e with
    | FnLetIn _ | FnRecord _ -> true
    | _ -> false
  in
  let on_case f e =
    match e with
    | FnLetIn (bindings, expr) ->
      let from_bindings =
        IM.of_alist
          (List.map
             (fun (v, e) ->
                let var = var_of_fnvar v in
                (var.vid, VarSet.inter vars (used_in_fnexpr e)))
             bindings)
      in
      let from_expr = f expr in
      IM.mapi
        (fun k deps ->
           VarSet.fold
             (fun var deps' ->
                try
                  (VarSet.union (IM.find var.vid from_bindings) deps')
                with Not_found ->
                  deps')
             deps deps)
        from_expr


    | FnRecord (vs, emap) ->
      IM.map used_in_fnexpr emap

    | _ -> failhere __FILE__ "collect_dependencies" "Bad case."
  in
  rec_expr2
    {
      join = join_depmap;
      on_case = on_case;
      case = case;
      init = IM.empty;
      on_var = (fun c -> IM.empty);
      on_const = (fun c -> IM.empty);
    }
    func


let rank_and_cluster (vars : VarSet.t) (deps : VarSet.t IM.t) : VarSet.t list =
  (* Search for variables that depend only on themselves *)
  let deps_sorted =
    (List.sort (fun (v1,i1) (v2,i2) -> compare i1 i2)
       (List.map
          (fun (i, card) -> (VarSet.find_by_id vars i, card))
          (IM.to_alist
             (IM.map (fun vs -> VarSet.cardinal vs) deps))))
  in
  let rec satisfy var vdeps satisfied =
    let is_satisfied v =
      match satisfied with
      | [] -> false
      | l -> (List.exists (fun vs -> VarSet.mem v vs) l)
    in
    VarSet.fold
      (fun dep to_sat ->
         if is_satisfied dep then to_sat
         else VarSet.add
             dep
             to_sat)
      vdeps
      (VarSet.singleton var)
  in
  let rec build_clusters vlist accum =
    match vlist with
    | [] -> accum
    | (var, dep_no) :: tl ->
      let cluster, remainder =
        let vdeps = IM.find var.vid deps in
        let cluster = satisfy var vdeps accum in
        cluster,
        (List.filter (fun (v,i) -> not (VarSet.mem v cluster)) tl)
      in
      build_clusters remainder (accum@[cluster])
  in
  snd (List.fold_left
         (fun (last, acc) cluster ->
            let se = VarSet.union last cluster in
            (se, acc@[se]))
         (VarSet.empty, [])
         (build_clusters deps_sorted []))




let get_dependent_subsets (problem : prob_rep) : VarSet.t list =
  let dep_map =
    collect_dependencies problem.scontext.state_vars problem.main_loop_body
  in
  rank_and_cluster problem.scontext.state_vars dep_map


let get_increments (problem : prob_rep) : prob_rep list =
  let subsets = get_dependent_subsets problem in
  let rename_pb i pb =
    if i < List.length subsets - 1 then
      { pb with loop_name = pb.loop_name^"_part"^(string_of_int i) }
    else
      pb
  in
  if !verbose then
    begin
      Format.printf "@.[INFO] Incremental solving (sets):@.";
      List.iteri
        (fun i varset ->
           Format.printf "@[<v 4>    %i : %a@]@." i VarSet.pp_vs varset)
        subsets
    end;

  (List.mapi rename_pb (List.map (restrict problem) subsets))


let complete_simple_sketch (sketch : fnExpr) (solution : fnExpr) : fnExpr =
  let rec _cb hl cl =
    List.fold_left
      (fun hl' (vh, eh) ->
         match List.filter (fun (vc, ec) ->  vc = vh) cl with
         | [] -> hl'@[vh,eh]
         | hd :: tl -> hl'@[vh, snd hd])
      [] hl
  and _c h c =
    match h, c with
  | FnLetIn (bsk, esk) , FnLetIn (bsol, esol) ->
    FnLetIn (_cb bsk bsol, _c esk esol)

  | FnRecord(vs, emap) , FnRecord(vs', emap') ->
    FnRecord(vs,
             IM.mapi
               (fun i e -> try IM.find i emap' with Not_found -> e)
               emap)

  | _ -> h
  in
  _c sketch solution


let complete_increment ~inner:(inner:bool) (increment : prob_rep) (sol : prob_rep option) : prob_rep =
  match sol with
  | Some sol ->
    let prev_solution =
      if inner then sol.memless_solution else sol.join_solution
    in
    let incr_sketch =
      if inner then increment.memless_sketch else increment.join_sketch
    in
    let zero = FnConst (CInt 0) in
    let new_sketch =
      if has_loop (incr_sketch (zero, zero))  then
        begin if has_loop prev_solution then
            (* Match 'one on one' *)
            incr_sketch
          else
            (* Remove the variables that can be joined with
               a constant join from the sketch and append the
               join at the beginning.
            *)
            incr_sketch
        end
      else
        (* The incremental sketch is scalar. The prev solution should be too. *)
        (fun bnd -> complete_simple_sketch (incr_sketch bnd) prev_solution)
    in
    if inner then { increment with memless_sketch = new_sketch }
    else { increment with join_sketch = new_sketch }

  | None -> increment
