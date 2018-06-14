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
open Conf
open Format
open FuncTypes
open Incremental
open Str
open Utils
open Utils.PpTools


module Cg = Codegen
module ExpRed = ExpressionReduction
module L = Local
module C = Canalyst

let solve_incrementally = ref false
let verbose = ref false
let synthTimes = (Conf.get_conf_string "synth_times_log")


let solution_failed ?(failure = "") problem =
  printf "@.%sFAILED:%s Couldn't retrieve the solution from the parsed ast \
          of the solved problem of %s.@."
    (color "red") color_default problem.loop_name;
  if failure = "" then ()
  else
    (eprintf "@.[FAILURE] %s@." failure;
     failhere __FILE__ "solution_failed" problem.loop_name)


let solution_found
    ?(inner=false)
    (racket_elapsed : float)
    (parsed : RAst.expr list)
    (problem : prob_rep) =

  if !verbose then
    printf "@.%s%s[INFO] SOLUTION for %s %s:@.%a"
      (color "green")       (if inner then "(inner loop)" else "")
      problem.loop_name color_default RAst.pp_expr_list parsed;

  (* Open and append to stats *)
  let oc = open_out_gen
      [Open_wronly; Open_append; Open_creat; Open_text]
      0o666 synthTimes in
  Printf.fprintf oc "%s,%.3f\n" problem.loop_name racket_elapsed;

  let sol_info =
    try
      Cg.get_solved_sketch_info parsed
    with _ ->
      (solution_failed problem;
       failwith "Couldn't retrieve solution from parsed ast.")
  in
  (* Parse the body of the join. *)
  let translated_join_body =
    let join_sketch =
      if inner then
        problem.memless_sketch
      else
        problem.join_sketch
    in
    init_scm_translate
      problem.scontext.all_vars problem.scontext.state_vars;
    try
      let solver_sol = scm_to_fn sol_info.Cg.join_body in
      remove_hole_vars
        (match Sketch.Join.match_hole_to_completion join_sketch solver_sol with
         | Some precise_sol ->
           (Expressions.enormalize
              problem.scontext
              precise_sol)
         | None -> solver_sol)
    with
    | Failure s ->
      eprintf "[FAILURE] %s@." s;
      failwith "Failed to translate the solution in our \
                intermediate representation."
  in
  (**
     Parse the identity/inital state that has been synthesized, if there is one.
  *)
  init_scm_translate problem.scontext.all_vars problem.scontext.state_vars;
  let remap_init_values maybe_expr_list =
    match maybe_expr_list with
    | Some expr_list ->
      begin try
          List.fold_left2
            (fun map vid ast_expr ->
               IM.add vid ast_expr map)
            IM.empty
            (VarSet.vids_of_vs problem.scontext.state_vars) expr_list
        with Invalid_argument e ->
          failhere __FILE__ "remap_init_values" "Invalid_argument"
      end

    | None ->
      (** If auxiliaries have been created, the sketch has been solved
          without having to assign them a specific value. We can
          just create placeholders according to their type. *)
      concretize_aux
        (fun vid vi map ->
           IM.add vid
             (match vi.vtype with
              | Integer -> RAst.Int_e 0
              | Boolean -> RAst.Bool_e true
              | Real -> RAst.Int_e 1
              | _ -> RAst.Nil_e) map)
        IM.empty
  in
  let remap_ident_values maybe_expr_list =
    match maybe_expr_list with
    | Some expr_list ->
      begin try
          (List.fold_left2
             (fun imap vid expr ->
                IM.add vid (scm_to_const expr) imap)
             IM.empty
             (VarSet.vids_of_vs problem.scontext.state_vars)
             expr_list)
        with Invalid_argument e ->
          failhere __FILE__ "remap_ident_values" "Invalid_argument"
      end
    | None -> IM.empty
  in
  let solution_0 = ExpRed.normalize problem.scontext translated_join_body in
  let solution = ExpRed.clean problem.scontext solution_0 in
  let init_vals = remap_init_values sol_info.Cg.init_values in
  let id_vals = remap_ident_values sol_info.Cg.identity_values in
  if inner then
    {problem with memless_solution = solution;
                  init_values = init_vals;
                  identity_values = id_vals}
  else
    {problem with join_solution = solution;
                  init_values = init_vals;
                  identity_values = id_vals}


let call_solver ?(inner=false) (ctx : context option) (pb : prob_rep) :
  float * prob_rep option =
  let t_elapsed, parsed =
    L.compile_and_fetch Conf.rosette
      ~print_err_msg:Racket.err_handler_sketch
      (C.pp_sketch ~inner:inner ~parent_context:ctx Conf.rosette)
      pb
  in
  if List.exists (fun e -> (RAst.Str_e "unsat") = e) parsed then
    t_elapsed, None
  else
    begin try
        let sol =
          Some (solution_found ~inner:inner t_elapsed parsed pb)
        in
        if inner then
          C.store_solution sol;
        t_elapsed, sol
      with Failure s ->
        (solution_failed ~failure:s pb;
         t_elapsed, None)
    end


let call_solver_incremental
    ?(inner=false)
    (ctx : context option)
    (pb : prob_rep) :
  float * prob_rep option =
  let increments = get_increments pb in
  try
    List.fold_left
      (fun (et, solution) incr_pb ->
         let part_pb = complete_increment ~inner:inner incr_pb solution in
         if !verbose then
           printf "@[<v 4>[INFO] Partial problem %s:@;%a.@;Sketch:@;%a@]@."
             incr_pb.loop_name
             FPretty.pp_fnexpr part_pb.main_loop_body
             FPretty.pp_fnexpr (if inner then
                                  part_pb.memless_sketch
                                else
                                  part_pb.join_sketch);
         match call_solver ~inner:inner ctx part_pb with
         | et', Some sol ->
           store_partial
             sol.loop_name
             (sol.scontext.state_vars,
              if inner then sol.memless_solution else sol.join_solution);
           et +. et', Some sol

         | et', None -> raise Not_found) (0., None) increments
  with Not_found -> -1.0, None

let rec solve_one ?(inner=false) ?(expr_depth = 1) parent_ctx problem =
  (* Set the expression depth of the sketch printer.*)
  FPretty.holes_expr_depth := expr_depth;
  let lp_name = problem.loop_name in
  try
    message_start_subtask ("Solving sketch for "^problem.loop_name);
    (* Compile the sketch to a Racket file, call Rosette, and parse the
       solution. *)
    let racket_elapsed, parsed =
      (if !solve_incrementally then call_solver_incremental else call_solver)
        ~inner:inner parent_ctx problem
    in
    match parsed with
    | None ->
      begin
        printf
          "@.%sNO SOLUTION%s found for %s (solver returned unsat)."
          (color "orange") color_default lp_name;
        if !FPretty.skipped_non_linear_operator then
          (** Try with non-linear operators. *)
          (FPretty.reinit ~ed:expr_depth ~use_nl:true;
           solve_one parent_ctx problem)
        else
          (FPretty.reinit ~ed:expr_depth ~use_nl:false;
           None)
      end
    | Some pb -> Some pb
  with Failure s ->
    (solution_failed ~failure:s problem;
     None)
      (* A solution has been found *)
