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
  let inline_join in_info =
    let join = in_info.memless_solution in
    match join with
    | FnLetExpr bl ->
      if List.length bl > 0 then
        Some (FnFun join)
      else None
    | _ -> None
  in
  let replace (lbody, ctx) in_info =
    let state = in_info.scontext.state_vars in
    let new_seq_type = Tuple (VarSet.types state) in
    let new_seq =
      mkFnVar (Conf.seq_name in_info.loop_name) new_seq_type
    in
    (* In case join cannot be inlined. *)
    let argtypes = Tuple [new_seq_type; new_seq_type] in
    let new_joinf_typ = Function (argtypes, new_seq_type) in
    let new_joinf =
      mkFnVar (Conf.join_name in_info.loop_name) new_joinf_typ
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
        (match inline_join in_info with
        | None ->
          FnApp (new_seq_type, Some new_joinf,
                 [FnVar(FnTuple state);FnVar(FnVariable(new_seq))])
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
    (transform_expr2 rpl_transformer lbody,
     {ctx with all_vars = VarSet.add new_seq ctx.all_vars;
               used_vars = VarSet.add new_seq ctx.used_vars;})
  in
  let newbody, newctx =
    List.fold_left replace (problem.loop_body, problem.scontext) inner_loops
  in
  {problem with inner_functions = inner_loops;
                scontext = newctx;
                loop_body = newbody;}
