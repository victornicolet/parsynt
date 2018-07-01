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
open Format
open Fn
open FnPretty
open FnDep
open SymbExe
open Utils


let verbose = ref false


let incremental_struct = ref ("", [])


let _partial_solutions : (VarSet.t * fnExpr) SH.t = SH.create 10


let store_partial s part = SH.add _partial_solutions s part


let get_opset_of_inner op variables : fnExpr -> VarSet.t =
  rec_expr2
    {
      join = VarSet.union;
      init = VarSet.empty;
      case = (fun e -> match e with FnRec _ -> true | _ -> false);
      on_case =
        (fun f e ->
           match e with
           | FnRec (_,(vs, _), _) ->  op vs variables
           | _ -> failwith "on-case failure, not FnRec");
      on_var = (fun v -> VarSet.empty);
      on_const = (fun v -> VarSet.empty);
    }


let get_diffset_of_inner : VarSet.t -> fnExpr ->  VarSet.t =
  get_opset_of_inner (VarSet.diff)


let get_subset_of_inner : VarSet.t -> fnExpr -> VarSet.t =
  get_opset_of_inner (VarSet.inter)


let get_inloop_info vars : fnExpr -> (VarSet.t * VarSet.t) =
  let _init = VarSet.empty, VarSet.empty in
  let _join s1 s2 =
    VarSet.union (fst s1) (fst s2),
    VarSet.union (snd s1) (snd s2)
  in
  let search_bindings blist =
    List.fold_left
      (fun (subs, bset) (v, e) ->
         match e with
         | FnRec(_,(vs,_),_) ->
           VarSet.diff vs vars, VarSet.singleton (var_of_fnvar v)
         | _ -> (subs, bset)) _init blist
  in
  rec_expr2
    {
      join = _join;
      init = _init;
      case = (fun e -> match e with FnLetIn _ -> true | _ -> false);
      on_case =
        (fun f e ->
           match e with
           | FnLetIn (blist, expr) ->
             _join (search_bindings blist) (f expr)
           | _ -> _init);

      on_var = (fun v -> _init);
      on_const = (fun v -> _init);
    }


let rec restrict_func
    (old_ctx : context) (variables : VarSet.t) (func : fnExpr) : fnExpr =

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
    match stl' with
    | [] -> Bottom
    | _ -> Record(name', stl')
  in
  let cases e =
    match e with
    | FnLetIn _ | FnRec _ | FnRecord _  -> true
    | _ -> false
  in

  let maybe_sub v =
    match v with
    | FnVariable var ->
      begin
        match var.vtype with
        (* Restrict the record type *)
        | Record (name, stl) ->
          let new_rtype = update_rectype name stl in
          if new_rtype = var.vtype then
            (*  No need for a new variable, but keep identity sub. *)
            Some (var, var)
          else
            Some (var, mkFnVar "x_" new_rtype)

        (* No restriction. *)
        | _ -> None
      end
    | _ -> None
  in

  let restrict_bindings f bds =
    List.map
      (fun (v,e) ->
         match maybe_sub v with
         | Some (ov, nv) -> Some(ov, nv), (mkVar nv, f e)
         | None -> None, (v, f e))
      (List.filter
         (fun (v,e) ->
            let var = var_of_fnvar v in
            match var.vtype with
            | Record(name, stl) ->
              begin match update_rectype name stl with
                | Bottom -> false
                | _ -> true
              end
            | _ -> VarSet.mem (var_of_fnvar v) variables) bds)
  in

  let restrict_body f e =
    match e with
    | FnLetIn (bindings, expr) ->
      begin match restrict_bindings f bindings with
        | [] -> f expr
        | l ->
          let substs, bindings = ListTools.unpair l in
          let true_substs = somes substs in
          let nexpr =
            List.fold_left
              (fun nexpr (ovar, nvar) ->
                 replace_expression (mkVarExpr ovar) (mkVarExpr nvar) nexpr)
              expr true_substs
          in
          FnLetIn(bindings, f nexpr)
      end

    | FnRecord(vs, emap) ->
      let nvs = VarSet.inter variables vs in
      FnRecord(nvs,
               IM.map f (IM.filter (fun k e -> VarSet.has_vid nvs k) emap))

    | FnRec ((i,g,u),(vs,bs),(s,body)) ->
      let nvs = VarSet.inter variables vs in
      let s' = mkFnVar "s" (record_type nvs) in
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
      on_var = identity;
      on_const = identity;
    }
    func


let rec restrict (pb : prob_rep) (variables : VarSet.t) : prob_rep =
  let new_body =
    restrict_func pb.scontext variables pb.main_loop_body
  in
  let rec_seq_var =
    let diffset = get_subset_of_inner variables pb.main_loop_body in
    mkFnVar "A" (Vector (record_type diffset, None))
  in
  let new_context =
    let ctr = ctx_inter pb.scontext variables in
    (* This assumes the only used vars that are record sequences are the
       summarized input of the summarized outer loop.
       See InnerFuncs.ml, L43 (transform_rl_vars)
    *)
    let update_record_sequences var =
      match var.vtype with
      | Vector(Record(sname, stl), _) ->
        rec_seq_var
      | _ -> var
    in
    {
      ctr with
      used_vars = VarSet.map update_record_sequences ctr.used_vars;
      all_vars = VarSet.map update_record_sequences ctr.all_vars;
    }
  in
  SketchJoin.sketch_inner_join
    (SketchJoin.sketch_join
       {
         pb with
         scontext = new_context;
         inner_functions = [];
         main_loop_body = new_body;
         loop_body_versions = SH.create 5;
       })



let get_dependent_subsets (problem : prob_rep) : VarSet.t list =
  let dep_map =
    let f k d =
      VarSet.inter problem.scontext.state_vars
        (VarSet.filter (fun v -> v.vid != k) d)
    in
    IM.mapi f
    (collect_dependencies problem.scontext problem.main_loop_body)
  in
  if !verbose then
    begin
      printf "[INFO] Dependencies:@.";
      IM.iter (fun k deps ->
          printf "    %s <-- %a@."
            (VarSet.find_by_id problem.scontext.all_vars k).vname
            VarSet.pp_var_names deps) dep_map;
    end;
  rank_and_cluster problem.scontext.state_vars dep_map


let get_increments (problem : prob_rep) : prob_rep list =
  let pb =
    InnerFuncs.inline_inner ~inline_pick_join:true (Dimensions.width ()) problem
  in

  let subsets = get_dependent_subsets pb in
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
  List.mapi rename_pb (List.map (restrict pb) subsets)


(**
   ----------------------------------------------------------------------

   Incremental completion of the sketch. Given a solution for the previous
   sketch in the incremental solving, fill in some of the holes of the
   current sketch.
*)

let complete_scalar_sketch (sketch : fnExpr) (solution : fnExpr) : fnExpr =
  let rec _cb hl cl =
    List.fold_left
      (fun hl' (vh, eh) ->
         match List.filter (fun (vc, ec) -> var_of_fnvar vc = var_of_fnvar vh) cl with
         | [] -> hl'@[vh,eh]
         | hd :: tl ->
           hl'@[fst hd, snd hd])
      [] hl
  and _c h flat_c =
    (* Only scalar variables: aasignments 'in parallel' can be flattened. *)
    match h with
    | FnLetIn(hl, he) ->
      FnLetIn(_cb hl flat_c, _c he flat_c)

    | FnRecord(hvs, hemap) ->
      wrap_state (_cb (unwrap_state hvs hemap) flat_c)

    | _ -> h
  in
  _c sketch (flat_bindings solution)



let complete_simple_sketch (sketch : fnExpr) (solution : fnExpr) : fnExpr =
  let rec _cb hl cl =
    List.fold_left
      (fun hl' (vh, eh) ->
         match List.filter (fun (vc, ec) -> var_of_fnvar vc = var_of_fnvar vh) cl with
         | [] -> hl'@[vh,eh]
         | hd :: tl ->
           hl'@[fst hd, snd hd])
      [] hl
  and _c h c =
    match h, c with
    | FnLetIn (bsk, FnLetIn(bsk2, esk)), FnLetIn (bsol, esol) ->
      let common1, common2 =
        let a1 = fst(used_in_assignments bsk) in
        let a2 = fst(used_in_assignments bsk2) in
        let b = fst(used_in_assignments bsol) in
        VarSet.cardinal (VarSet.inter a1 b),
        VarSet.cardinal (VarSet.inter a2 b)
      in
      if common1 > common2 then
        FnLetIn (_cb bsk bsol, FnLetIn (bsk2, _c esk esol))
      else
        FnLetIn (bsk, FnLetIn (_cb bsk2 bsol, _c esk esol))

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



let remove_from_loop_state (variables : VarSet.t) (sketch : fnExpr) : fnExpr =
  let diffset = get_diffset_of_inner variables sketch in
  let inner_proj_name = record_name diffset in
  let inner_proj_struct = record_type diffset in
  incremental_struct := (inner_proj_name, VarSet.names diffset);

  let loopres_binder, new_loopres_binder, new_inner_binder =
    let vars, binders = get_inloop_info variables sketch in
    let lb = VarSet.max_elt binders in
    lb,
    mkFnVar (lb.vname^"_part") inner_proj_struct,
    mkFnVar "s" inner_proj_struct
  in

  let change_loopres_binder v =
    match v with
    | FnVariable var when var = loopres_binder ->
      FnVariable new_loopres_binder
    | _ -> v
  in

  let change_binders =

    transform_expr2
      { case = (fun e -> false); on_case = (fun f e -> e); on_const = identity;
        on_var = change_loopres_binder;
      }
  in

  let transform_loop_body in_binder body =
    let case e =
      match e with
      | FnLetIn _ -> true
      | FnRecord _ -> true
      | FnRec _ -> true
      | _ -> false
    in
    let on_case f e =
      match e with
      | FnLetIn (bindings, expr) ->
        FnLetIn (
          List.map
            (fun (v, ve) -> (change_loopres_binder v, f ve))
            (List.filter
               (fun (v, ve) -> not (VarSet.mem (var_of_fnvar v) variables))
               bindings),
          f expr)

      | FnRecord (vs, emap) ->
        FnRecord (VarSet.diff vs variables,
                  IM.filter (fun k e -> not (VarSet.has_vid variables k)) emap)

      | _ -> failwith "on_case failure"
    in
    let on_var v =
      match v with
      | FnVariable var when var = in_binder ->
        FnVariable new_inner_binder

      | _ -> v
    in
    transform_expr2
      { case = case; on_case = on_case; on_var = on_var; on_const = identity }
      body
  in

  let transform_initial_state s init_expr =
    transform_loop_body s init_expr
  in

  transform_expr2
    { case = (fun e ->
          match e with
          |  FnRec _ | FnRecord _ | FnLetIn _ -> true
          | _ -> false);
      on_case =
        (fun f e ->
           match e with
           | FnRec (igu, (vs, bs), (s, body)) ->
             FnRec (igu, (VarSet.diff vs variables, transform_initial_state s
                            bs),
                    (new_inner_binder, remove_empty_lets
                       (transform_loop_body s body)))

           | FnRecord (vs, emap) ->
             FnRecord(vs,
                      IM.mapi (fun k e ->
                          try mkVarExpr (VarSet.find_by_id variables k)
                          with Not_found -> change_binders e) emap)
           | FnLetIn (blist, expr) ->
             FnLetIn (List.map (fun (v,e) -> (change_loopres_binder v, f e))
                        blist,
                      f expr)

           | _  -> failwith "on-case failure");
      on_var = identity;
      on_const = identity;
    } sketch


let compose_loop (sol : prob_rep) (prev_solution : fnExpr) (sketch : fnExpr) : fnExpr =
  let scalars, prev_sol =
    match prev_solution with
    | FnLetIn(scalars, FnLetIn([x1, FnRec (a,b,c)], r1)) ->
      scalars, FnLetIn([x1, FnRec (a,b,c)], r1)

    | FnLetIn([x1, FnRec _], r1) ->
      [] , prev_solution

    | _ -> failhere __FILE__ "compose_loop" "Bad top form."
  in
  let core =
    match prev_sol, sketch with
    | FnLetIn([x1, FnRec(_,_,(s1, bodysol))], r1),
      FnLetIn([x2, FnRec(igu, st2,(s2, bodysketch))], r2) ->
      let r =
        replace_expression (FnVar x1) (FnVar x2)
          (complete_simple_sketch r2 r1)
      in
      begin
        match bodysol, bodysketch with
        | FnLetIn(l1, e1), FnLetIn(l2, e2) ->
          let body = FnLetIn(l2, complete_simple_sketch e2 e1) in
          let res = FnLetIn([x2, FnRec(igu, st2, (s2, body))], r) in
          res

        | _ -> failhere __FILE__ "compose_loop" "Bad body form."
      end
    | _ -> failhere __FILE__ "compose_loop" "Bad top form."
  in
  match scalars with
  | [] -> core
  | _ -> FnLetIn(scalars, core)


let complete_increment
    ~inner:(inner:bool)
    (increment : prob_rep)
    (sol : prob_rep option) : prob_rep =
  match sol with
  | Some sol ->
    let prev_solution =
      if inner then sol.memless_solution else sol.join_solution
    in
    let incr_sketch =
      if inner then increment.memless_sketch else increment.join_sketch
    in
    let new_sketch =
      if has_loop incr_sketch  then
        begin if has_loop prev_solution then
            begin
              (* Match 'one on one' *)
              if !verbose then printf "[INFO] Loop solution, loop sketch.@.";
              compose_loop
                sol
                prev_solution
                incr_sketch
            end
          else
            begin
            (* Remove the variables that can be joined with
               a constant join from the sketch and append the
               join at the beginning.
            *)
              if !verbose then printf "[INFO] Scalar solution, loop sketch.@.";
            compose prev_solution
              (remove_from_loop_state
                 sol.scontext.state_vars
                 incr_sketch)
          end
        end
      else
        begin
          (* The incremental sk. is scalar. The prev solution should be too.*)
          if !verbose then printf "[INFO] Scalar sketch.@.";
          complete_scalar_sketch incr_sketch prev_solution
        end
    in
    if inner then { increment with memless_sketch = new_sketch }
    else { increment with join_sketch = new_sketch }

  | None -> increment
