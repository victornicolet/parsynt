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
open Fn
open Utils
open Format

let verbose = ref false

let _KEY_INNER_INLINED_ = "inner-inlined"
let _KEY_JOIN_NOT_INLINED_ = "join-not-inlined"
let _KEY_JOIN_INLINED_ = "join-inlined"

let transform_rl_vars cr_i out_index : fnExpr -> fnExpr =
  let rec _tv v =
    match v with
    | FnVariable vi ->
      let rvname, _, right = is_right_state_varname vi.vname in
      let lvname, _, left = is_left_state_varname vi.vname in
      if left then
        FnVariable (find_var_name lvname)
      else if right then
        let input_like = Conf.seq_name rvname in
        begin
          let v = try
              find_var_name input_like
            with Not_found ->
              mkFnVar input_like (Vector(vi.vtype, None))
          in
          IH.add cr_i v.vid v;
          FnArray(FnVariable v, out_index)
        end
      else
        FnVariable vi

    | FnArray (v, e) -> FnArray (_tv v,e)
  in
  transform_expr2
    {
      case = (fun e -> false);
      on_case = (fun f e -> e);
      on_var = _tv;
      on_const = identity;
    }



(**
   Replaces calls to inner loop function in the outer loop
    by a simplified version using the join of the inner loop or the memoryless
    version of the loop when possible.
   @param problem The current problem, where nothing is solved.
   @param inner_loops A map from loop ids to structures containing the
   information on the inner loop.
   @return The problem where inner loop info has been updated and the outer body
   has been simplified using all the information possible and updated variables
   with new sequences representing inner loop's outputs.
*)


let replace_by_join problem inner_loops =
  let created_inputs = IH.create 10 in

  let replace (lbody, ctx) in_info =
    IH.clear created_inputs;
    let out_index = mkVarExpr (VarSet.max_elt ctx.index_vars) in
    (* Create a sequence type for the input of the inner loop. *)
    let state = in_info.scontext.state_vars in
    let inner_styp = record_type state in

    let seq_inner = Vector (inner_styp, None) in
    let new_seq =
      mkFnVar (Conf.seq_name in_info.loop_name) seq_inner
    in
    register_fnv new_seq;
    (* In case join cannot be inlined. *)
    let new_joinf_typ = Function (inner_styp, inner_styp) in
    (* The function corresponding to the join. *)
    let new_joinf =
      try
        find_var_name (Conf.join_name in_info.loop_name)
      with Not_found ->
        mkFnVar (Conf.join_name in_info.loop_name) new_joinf_typ
    in
    let in_st, in_end = get_bounds in_info in
    (* Replace the function application corresponding to the inner loop.
       These were only placeholders introdced at the Cil intermediate
       representation.
    *)

    (* Inline the join only if it is only a record expression. *)
    let inline_join out_index in_info =
      let join = in_info.memless_solution in
      match join with
      | FnRecord(vs, emap) ->
        begin
          if IM.cardinal emap > 0 then
            let jn = transform_rl_vars created_inputs out_index join in
            Some jn

          else None
        end
      | _ -> None
    in
    let rpl_case e =
      match e with
      | FnApp (st, Some f, args) ->
        (Conf.is_inner_loop_func_name f.vname &&
         (Conf.id_of_inner_loop f.vname) = in_info.id)

      | _ -> false
    in
    let rpl rfunc e =
      match e with
      | FnApp (st, Some f, args) ->
        (match inline_join out_index in_info with
         | None ->

           if !verbose then
             printf
               "@.[INFO] Inner join %s is not inlined.@."
               in_info.loop_name;

           let capture_state =
             FnRecord (state, identity_map state)
           in
           let index = VarSet.max_elt problem.scontext.index_vars in
           FnApp (inner_styp, Some new_joinf,
                  [capture_state; mkVarExpr ~offsets:[mkVarExpr index] new_seq;
                   mkVarExpr in_st; mkVarExpr in_end])

         | Some inline_join ->

           if !verbose then
             printf "@.[INFO] Inner join %s is inlined.@." in_info.loop_name;

           inline_join)


      | _ -> rfunc e
    in
    let rpl_transformer =
      { case = rpl_case;
        on_case = rpl;
        on_const = (fun c -> c);
        on_var = (fun v -> v);
      }
    in
    let new_body = transform_expr2 rpl_transformer  lbody in
    let added_inputs =
      IH.fold
        (fun id v vset -> VarSet.add v vset) created_inputs
        (used_in_fnexpr new_body)
    in
    new_body, {ctx with all_vars = VarSet.union added_inputs ctx.all_vars;
                        used_vars = added_inputs }
  in
  let newbody, newctx =
    List.fold_left
      replace (problem.main_loop_body, problem.scontext) inner_loops
  in

  SH.add problem.loop_body_versions _KEY_JOIN_NOT_INLINED_
    problem.main_loop_body;
  SH.add problem.loop_body_versions _KEY_JOIN_INLINED_ newbody;

    {
      problem with
      inner_functions = inner_loops;
      scontext = newctx;
      main_loop_body = newbody;}


let no_join_inlined_body pb =
  try SH.find pb.loop_body_versions _KEY_JOIN_NOT_INLINED_
  with Not_found -> pb.main_loop_body


(* `inline_inner` replaces the calls to inner functions by either the solution
   of the memoryless join or the body of the inner loop.
   By default, it will pick the solution of the memoryless/inner join.
   To switch to inner functions, call with ~inline_pick_join:false.
   @param `in_loop_width` The loop inlined has to be finitized for symbolic
   execution and join synthesis, in_loop_width is the finitization limit.
   @param `problem` is the problem where the loop needs to be inlined, the
   resulting loop body will be the main_loop_body of the problem returned.
   It will inline in the loop body returned by no_join_inlined_body. If there
   is the corresponding entry  _KEY_JOIN_NOT_INLINED_ in the loop versions,
   if will use this one, otherwise the main_loop_body.
*)
let inline_inner ?(inline_pick_join=true) in_loop_width problem =
  if !verbose then
    printf "@.[INFO] @[<v 4>Outer function before inlining:@;%a@]@."
      FnPretty.pp_fnexpr (no_join_inlined_body problem);

  let inner_loop_ids = List.map (fun pin -> pin.id) problem.inner_functions in
  let created_inputs = IH.create 5 in

  let inline_inner in_info args =
    let in_body = no_join_inlined_body in_info in
    let in_state = in_info.scontext.state_vars in
    let in_type = record_type in_state in
    let in_index = VarSet.max_elt in_info.scontext.index_vars in
    let in_binder = mkFnVar ("$"^(string_of_int in_info.id)^"s") in_type in
    let map_args =
      IM.of_alist (List.combine (VarSet.vids_of_vs in_state) args)
    in
    if !verbose then
      printf
        "[WARNING] Inlined inner function iterates from 0 to %i by default.@."
        in_loop_width;
    let inlined =
      FnRec((
        FnConst (CInt 0),
        FnBinop(Lt, mkVarExpr in_index, FnConst (CInt in_loop_width)),
        FnBinop(Plus, mkVarExpr in_index, FnConst (CInt 1))),
        (in_state, FnRecord(in_state, map_args)),
        (in_binder,
         FnLetIn
           (bind_state ~prefix:"" ~state_rec:in_binder ~members:in_state,
            in_body)))
    in
    inlined
  in

  let inline_join s in_info args =
    let j_start, j_end = get_bounds in_info in
    let repl_start e =
      replace_expression ~in_subscripts:true
        ~to_replace:(mkVarExpr j_start) ~by:(FnConst (CInt 0)) ~ine:e
    in
    let repl_end e =
      replace_expression ~in_subscripts:true
        ~to_replace:(mkVarExpr j_end) ~by:(FnConst (CInt in_loop_width)) ~ine:e
    in
    (**
       If the solution is of the form loop + choice bindings, extract the loop,
       and push the bindings to the outer loop.
    *)
    let in_body, new_unwrap =
      let replaced_rl =
        transform_rl_vars
          created_inputs
          (mkVarExpr (VarSet.max_elt (get_index_varset problem)))
          ((repl_start --> repl_end) in_info.memless_solution)
      in
      match replaced_rl with
      | FnLetIn([loop_res, FnRec (igu, vsbs, loopdef)], FnRecord(in_state, choices)) ->
        let choices' =
          IM.map
            (fun e ->
               replace_expression
                 ~in_subscripts:false
                 ~to_replace:(FnVar loop_res)
                 ~by:(FnVar s)
                 ~ine:e) choices
        in
        FnRec (igu, vsbs, loopdef),
        Some (unwrap_state in_state choices')

      | FnLetIn(prescalar,
                FnLetIn([loop_res, FnRec (igu, vsbs, loopdef)], FnRecord(in_state, choices))) ->
        let sub er (v,e) =
          replace_expression
            ~in_subscripts:false
            ~to_replace:(FnVar v)
            ~by:e
            ~ine:er
        in
        let f e =
          let e' = replace_expression
            ~in_subscripts:false
            ~to_replace:(FnVar loop_res)
            ~by:(FnVar s)
            ~ine:e
          in
          List.fold_left sub e' prescalar
        in
        let choices' = IM.map f choices in
        FnRec (igu, vsbs, loopdef),
        Some (unwrap_state in_state choices')

      | e ->  e, None
    in

    if !verbose then
      printf
        "[WARNING] Inlined inner join iterates from 0 to %i by default.@."
        in_loop_width;

    in_body, new_unwrap
  in

  let inline_case e =
    match e with
    | FnLetIn([lrb, FnApp(st, Some f, args)], FnLetIn(unwrap_lrb, expr)) ->
      (Conf.is_inner_loop_func_name f.vname) &&
      (List.mem (Conf.id_of_inner_loop f.vname) inner_loop_ids)

    | _ -> false
  in

  let inline rfunc e =
    match e with
    | FnLetIn([lrb, FnApp(st, Some f, args)], FnLetIn(unwrap_lrb, expr)) ->
      let infun, new_unwraps =
        if inline_pick_join then
          let injoin, new_unwrap =
            inline_join lrb
              (List.find (fun pin ->
                   pin.id = (Conf.id_of_inner_loop f.vname))
                  problem.inner_functions) args
          in
          match new_unwrap with
          | Some l -> injoin, l
          | None -> injoin, unwrap_lrb
        else
          let injoin =
                      inline_inner
            (List.find (fun pin ->
                 pin.id = (Conf.id_of_inner_loop f.vname))
               problem.inner_functions) args
          in
          injoin, unwrap_lrb
      in
      FnLetIn([lrb, infun], FnLetIn(new_unwraps, expr))


    | _ -> rfunc e
  in
  let cur_loop_body = no_join_inlined_body problem in
  let loop_body' =
    transform_expr2
      { case = inline_case;
        on_case = inline;
        on_var = identity;
        on_const = identity } cur_loop_body
  in
  if !verbose then
    begin if loop_body' != cur_loop_body then
        printf "[INFO] @[<v 4>Outer function after inlining:@;%a@]@."
          FnPretty.pp_fnexpr loop_body'
      else
        printf "[INFO] Outer function after inlining unchanged.@.";
    end;

  let new_vars =
    IH.fold (fun k v vs -> VarSet.add v vs) created_inputs VarSet.empty
  in
  SH.add problem.loop_body_versions _KEY_INNER_INLINED_ loop_body';
  { problem with
    main_loop_body = loop_body';
    scontext =
      {problem.scontext with
       used_vars = VarSet.union problem.scontext.used_vars new_vars;
       all_vars = VarSet.union problem.scontext.all_vars new_vars;
      }
  }



let inner_inlined_body pb =
  try SH.find pb.loop_body_versions _KEY_INNER_INLINED_
  with Not_found -> pb.main_loop_body


let update_inners_in_body
    (inners : (prob_rep * prob_rep) list)
    (body : fnExpr) : fnExpr =
  let upd body (old_inner, new_inner) =
    let old_rname = record_name old_inner.scontext.state_vars in
    let all_record_accessors l =
      if
        List.length l > 0 &&
        List.for_all
          (fun (v,e) ->
             match e with
             | FnRecordMember(ev, s) -> true
             | _ -> false) l
      then
        begin
          match List.hd l with
          | _, FnRecordMember(FnVar(FnVariable var), _) -> Some var
          | _ -> None
        end
      else
        None
    in
    let case e =
      match e with
      | FnVar (FnVariable v) ->
        begin match v.vtype with
          | Record (ols, _) when ols = old_rname -> true
          | t -> false
        end

      | FnLetIn _ -> true

      | _ -> false
    in
    let on_case f e =
      match e with
      | FnVar (FnVariable v) ->
        let typ = match v.vtype with
          | Record (ols, _) when ols = old_rname ->
            record_type new_inner.scontext.state_vars
          | t -> t
        in FnVar(FnVariable {v with vtype = typ})

      | FnLetIn(binds, expr) ->
        begin match all_record_accessors binds with
          | Some x ->
            let x' =
              {x with vtype = record_type new_inner.scontext.state_vars}
            in
            FnLetIn(bind_state x' new_inner.scontext.state_vars, f expr)
          | None ->
            FnLetIn(List.map (fun (v,e) -> (v, f e)) binds, f expr)
        end
      | _ -> e
    in
    transform_expr2
      {
        case = case;
        on_case = on_case;
        on_var = identity;
        on_const = identity;
      }
      body
  in
  List.fold_left upd body inners


let uses_inner_join_func : fnExpr -> bool =
  rec_expr2 {
    join = (||);
    init = false;
    case = (fun e -> match e with FnApp _ -> true | _ -> false);
    on_case =
      (fun f e ->
         match e with
         | FnApp(_, Some v, _) ->
           Conf.is_inner_join_name v.vname
         | _ -> false);
    on_var = (fun v -> false);
    on_const = (fun c -> false);
  }
