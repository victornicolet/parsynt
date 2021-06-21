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
open Sketch
open Format
open Utils
open Fn
open VariableDiscovery

let debug = ref false

let verbose = ref false

type sigu = VarSet.t * (fnExpr * fnExpr * fnExpr)

(* Function to convert a subproblem into a loop body *)
let convert (problem : prob_rep) : prob_rep =
  let pb =
    InnerFuncs.inline_inner ~index_variable:true ~inline_pick_join:false (Dimensions.width ())
      problem
  in
  problem.inner_functions <- [];
  pb

(*
   From intermediary representation with contained expressions to final
   functional representation.
*)
let no_sketches = ref 0

let func2sketch _cfile _funcreps =
  (* SH.add lversions "orig" loop_body;
     let fn_pb =
       {
         id = func_info.lid;
         host_function = host_func;
         loop_name = func_info.loop_name;
         scontext =
           {
             state_vars;
             index_vars = fst sigu;
             used_vars = varset_of_vs func_info.lvariables.used_vars;
             all_vars = varset_of_vs func_info.lvariables.all_vars;
             costly_exprs = ES.empty;
           };
         min_input_size = max_m_sizes;
         uses_global_bound = uses_global_bounds;
         main_loop_body = loop_body;
         loop_body_versions = lversions;
         join_sketch = empty_record;
         memless_sketch = empty_record;
         (* No solution for now! *)
         join_solution = empty_record;
         memless_solution = empty_record;
         init_values = IM.empty;
         identity_values = IM.empty;
         func_igu = sigu;
         reaching_consts = s_reach_consts;
         inner_functions = inners;
       }
       (* Added to limit the depth in case depth = *)
     in
     let fn_pb =
       if List.length fn_pb.inner_functions = 0 || depth = 0 then fn_pb
       else
         let aux = convert fn_pb in
         fprintf Format.std_formatter "Succesful inlining \n";
         aux
     in
     VarSet.iter register_fnv fn_pb.scontext.all_vars;
     VarSet.iter register_fnv fn_pb.scontext.index_vars;
     Sketch.Join.sketch_inner_join (Sketch.Join.sketch_join fn_pb) *)
  (* in *)
  (* let probs = List.map transform_func funcreps in *)
  (* Do igus first, and then arrays. otherwise this will create errors. *)
  (* List.iter Dimensions.register_dimensions_igu probs;
     List.iter Dimensions.register_dimensions_arrays probs; *)
  (* if !verbose then Dimensions.print_status (); *)
  ()

(**
   Finds auxiliary variables necessary to parallelize the function.
   @param sketch_rep the problem representation.
   @return a new problem represention where the function and the variables
   have been modified.
*)
let find_new_variables prob_rep =
  let new_prob =
    try discover prob_rep
    with VariableDiscoveryError s ->
      eprintf "[ERROR] Failed to discover new variables.@.";
      raise (VariableDiscoveryError s)
  in
  (* Apply some optimization to reduce the size of the function *)
  discover_save ();

  let inners = List.map Sketch.Join.sketch_inner_join new_prob.inner_functions in

  let new_loop_body =
    let nlb_opt = (* In old code: Func2Fn.optims. *) new_prob.main_loop_body in
    let nlb = complete_final_state new_prob.scontext.state_vars nlb_opt in
    InnerFuncs.update_inners_in_body (List.combine prob_rep.inner_functions inners) nlb
  in

  SH.clear new_prob.loop_body_versions;
  Sketch.Join.sketch_join { new_prob with main_loop_body = new_loop_body; inner_functions = inners }

let pp_sketch ?(inner = false) ?(parent_context = None) solver fmt sketch_rep =
  let parent_context =
    if inner then
      match parent_context with
      | Some context -> context
      | None -> failhere __FILE__ "pp_sketch" "Parent context not provided for child loop."
    else mk_ctx VarSet.empty VarSet.empty
  in
  match solver.Config.name with
  | "Rosette" ->
      copy_aux_to Sketch.auxiliary_vars;
      Sketch.pp_rosette_sketch parent_context inner fmt sketch_rep
  | _ -> ()

let store_solution = Join.store_solution

let clear () =
  discover_clear ();
  Base.Hashtbl.clear Sketch.auxiliary_vars
