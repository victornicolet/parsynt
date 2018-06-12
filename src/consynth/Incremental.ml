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
  {
    problem with
    scontext = ctx_inter problem.scontext variables;
    main_loop_body = new_body;
    loop_body_versions = SH.create 5;
  }


let collect_dependencies vars func =
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
    | FnLetIn (bindings, cont) ->
      join_depmap
        (IM.of_alist
           (List.map
              (fun (v, e) ->
                 let var = var_of_fnvar v in
                 (var.vid, VarSet.inter vars (used_in_fnexpr e)))
              bindings))
        (f e)

    | FnRecord (vs, emap) -> IM.empty
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

let get_dependent_subsets (problem : prob_rep) : VarSet.t list =
  let dep_map =
    collect_dependencies problem.scontext.state_vars problem.main_loop_body
  in
  rank_and_cluster problem.scontext.state_vars dep_map

let get_increments (problem : prob_rep) : prob_rep list =
  let subsets = get_dependent_subsets problem in
  (List.map (restrict problem) subsets)

let complete_increment (increment : prob_rep) (sol : prob_rep option) =
  increment
