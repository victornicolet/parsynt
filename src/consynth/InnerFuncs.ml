(**
   This file is part of Parsynt.

    Foobar is free software: you can redistribute it and/or modify
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
open Format

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
  (* Inline the join only if it is a list of parallel assignments. *)
  let inline_join out_index in_info =
    let join = in_info.memless_solution in
    match join with
    | FnLetExpr bl ->
      begin

        if List.length bl > 0 then

        let rec transform_var : fnLVar -> fnLVar =
          function
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
                IH.add created_inputs v.vid v;
                FnArray(FnVariable v, out_index)
              end
            else
              FnVariable vi

          | FnArray (v, e) -> FnArray (transform_var v,e)
        in
        let jn =
          transform_expr2
            {
              case = (fun e -> false);
              on_case = (fun f e -> e);
              on_var = transform_var;
              on_const = identity;
            } join
        in
        Some jn

        else None
      end
    | _ -> None
  in
  let replace (lbody, ctx) in_info =
    IH.clear created_inputs;
    let out_index = mkVarExpr (VarSet.max_elt ctx.index_vars) in
    (* Create a sequence type for the input of the inner loop. *)
    let state = in_info.scontext.state_vars in
    let inner_styp = Record (VarSet.record state) in

    let seq_inner = Vector (inner_styp, None) in
    let new_seq =
      mkFnVar (Conf.seq_name in_info.loop_name) seq_inner
    in
    register_fnv new_seq;
    (* In case join cannot be inlined. *)
    let new_joinf_typ = Function (inner_styp, inner_styp) in
    (* The function corresponding to the join. *)
    let new_joinf =
      mkFnVar (Conf.join_name in_info.loop_name) new_joinf_typ
    in
    let in_st, in_end = get_bounds in_info in
    (* Replace the function application corresponding to the inner loop.
       These were only placeholders introdced at the Cil intermediate
       representation.
    *)
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
           let capture_state =
             FnRecord (Record (VarSet.record state),
                       List.map mkVarExpr (VarSet.elements state))
           in
           let index = VarSet.max_elt problem.scontext.index_vars in
           FnApp (inner_styp, Some new_joinf,
                  [capture_state; mkVarExpr ~offsets:[mkVarExpr index] new_seq;
                   mkVarExpr in_st; mkVarExpr in_end])

         | Some inline_join ->
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
    let new_body = transform_expr2 rpl_transformer lbody in
    let added_inputs =
      IH.fold
        (fun id v vset -> VarSet.add v vset) created_inputs
        (used_in_fnexpr new_body)
    in
    new_body, {ctx with all_vars = VarSet.union added_inputs ctx.all_vars;
                        used_vars = added_inputs }
  in
  let newbody, newctx =
    List.fold_left replace (problem.loop_body, problem.scontext) inner_loops
  in
  let new_sketch =
    Sketch.Join.build_join
      (List.map
         (fun pb -> mkVarExpr (VarSet.max_elt pb.scontext.index_vars))
         problem.inner_functions)
      problem.scontext.state_vars newbody
  in
  {problem with inner_functions = inner_loops;
                join_sketch = new_sketch;
                scontext = newctx;
                loop_body = newbody;}
