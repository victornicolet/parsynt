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

open Singleloop
open Sygus
open Beta
open Format
open Fn
open Incremental
open Utils
module Cg = Codegen
module ExpRed = ExpressionReduction
module L = Local
module C = Canalyst

let _incr_timeout_ = Config.get_conf_int "base_incr_timeout"

let timeout_multiplier = ref 1

let solve_incrementally = ref false

let verbose = ref false

let synthTimes = Config.get_conf_string_exn "synth_times_log"

let solution_failed ?(failure = "") problem =
  Log.error_msg
    Fmt.(
      str "Couldn't retrieve the solution from the parsed ast of the solved problem of %s.@."
        problem.loop_name);
  if failure = "" then ()
  else (
    eprintf "@.[FAILURE] %s@." failure;
    failhere __FILE__ "solution_failed" problem.loop_name)

let solution_found ?(inner = false) (racket_elapsed : float) (parsed : RAst.expr list)
    (problem : prob_rep) =
  if !verbose then
    Log.info_msg
      Fmt.(
        str "SOLUTION for %s %s:@.%a"
          (if inner then "(inner loop)" else "")
          problem.loop_name RAst.pp_expr_list parsed);
  (* Open and append to stats *)
  let oc = open_out_gen [ Open_wronly; Open_append; Open_creat; Open_text ] 0o666 synthTimes in
  Printf.fprintf oc "%s,%.3f\n" problem.loop_name racket_elapsed;

  let sol_info =
    try Codegen.get_solved_sketch_info parsed
    with _ ->
      solution_failed problem;
      failwith "Couldn't retrieve solution from parsed ast."
  in
  (* Parse the body of the join. *)
  let translated_join_body =
    let sketch = if inner then problem.memless_sketch else problem.join_sketch in
    init_scm_translate problem.scontext.all_vars problem.scontext.state_vars;
    try
      let solver_sol = scm_to_fn sol_info.Cg.join_body in
      remove_hole_vars
        (match Sketch.Join.match_hole_to_completion sketch solver_sol with
        | Some precise_sol -> Expressions.enormalize problem.scontext precise_sol
        | None -> solver_sol)
    with Failure s ->
      eprintf "[FAILURE] %s@." s;
      failwith "Failed to translate the solution in our intermediate representation."
  in
  (*
     Parse the identity/inital state that has been synthesized, if there is one.
  *)
  init_scm_translate problem.scontext.all_vars problem.scontext.state_vars;
  let remap_init_values maybe_expr_list =
    match maybe_expr_list with
    | Some expr_list -> (
        try
          List.fold_left2
            (fun map vid ast_expr -> IM.set vid ast_expr map)
            IM.empty
            (VarSet.vids_of_vs problem.scontext.state_vars)
            expr_list
        with Invalid_argument _ -> failhere __FILE__ "remap_init_values" "Invalid_argument")
    | None ->
        (* If auxiliaries have been created, the sketch has been solved
            without having to assign them a specific value. We can
            just create placeholders according to their type. *)
        concretize_aux
          (fun vid vi map ->
            IM.set vid
              (match vi.vtype with
              | Integer -> RAst.Int_e 0
              | Boolean -> RAst.Bool_e true
              | Real -> RAst.Int_e 1
              | _ -> RAst.Nil_e)
              map)
          IM.empty
  in
  let remap_ident_values maybe_expr_list =
    match maybe_expr_list with
    | Some expr_list -> (
        try
          List.fold_left2
            (fun imap vid expr -> IM.set vid (scm_to_const expr) imap)
            IM.empty
            (VarSet.vids_of_vs problem.scontext.state_vars)
            expr_list
        with Invalid_argument _ -> failhere __FILE__ "remap_ident_values" "Invalid_argument")
    | None -> IM.empty
  in
  let solution_0 = ExpRed.normalize problem.scontext translated_join_body in
  let solution = ExpRed.clean problem.scontext solution_0 in
  let init_vals = remap_init_values sol_info.Cg.init_values in
  let id_vals = remap_ident_values sol_info.Cg.identity_values in
  if inner then
    { problem with memless_solution = solution; init_values = init_vals; identity_values = id_vals }
  else { problem with join_solution = solution; init_values = init_vals; identity_values = id_vals }

let call_solver ?(timeout = -1) ?(inner = false) (ctx : context option) (pb : prob_rep) :
    float * prob_rep option =
  let rec solve_for_depth d0 dmax =
    if !verbose then
      printf "[INFO]%sSearching at depth %i...@."
        (if timeout > 0 then "(TIMEOUT=" ^ string_of_int timeout ^ ") " else "")
        d0;

    let t, p =
      let new_timeout = timeout * (d0 + 1) in
      L.compile_and_fetch Config.rosette ~timeout:new_timeout
        ~print_err_msg:Racket.err_handler_sketch
        (C.pp_sketch ~inner ~parent_context:ctx Config.rosette)
        (set_pb_hole_depths pb d0)
    in
    if List.exists (fun e -> RAst.Str_e "unsat" = e) p || p = [] then
      if d0 = dmax then (t, None) else solve_for_depth (d0 + 1) dmax
    else (t, Some p)
  in
  let t_elapsed, maybe_parsed_sol = solve_for_depth 0 2 in
  match maybe_parsed_sol with
  | Some parsed -> (
      try
        let sol = Some (solution_found ~inner t_elapsed parsed pb) in
        if inner then C.store_solution sol;
        (t_elapsed, sol)
      with Failure s ->
        solution_failed ~failure:s pb;
        (t_elapsed, None))
  | None -> (-1.0, None)

let call_solver_incremental ?(inner = false) (ctx : context option) (pb : prob_rep) :
    float * prob_rep option =
  let tmout = _incr_timeout_ * !timeout_multiplier in
  let increments = get_increments pb in
  try
    List.fold_left
      (fun (et, solution) incr_pb ->
        let part_pb = complete_increment ~inner incr_pb solution in
        if !verbose then
          Log.info_msg
            Fmt.(
              str "@.@[<v 4>[INFO] Partial problem %s:@;%a.@;Sketch:@;%a@]@." incr_pb.loop_name
                FnPretty.pp_fnexpr part_pb.main_loop_body FnPretty.pp_fnexpr
                (if inner then part_pb.memless_sketch else part_pb.join_sketch));
        match call_solver ~timeout:tmout ~inner ctx part_pb with
        | et', Some sol ->
            store_partial sol.loop_name
              (sol.scontext.state_vars, if inner then sol.memless_solution else sol.join_solution);
            (et +. et', Some sol)
        | _, None -> raise Not_found)
      (0., None) increments
  with Not_found -> (-1.0, None)

let rec solve_one ?(inner = false) ?(expr_depth = 1) parent_ctx problem =
  (* Set the expression depth of the sketch printer.*)
  let lp_name = problem.loop_name in
  try
    Log.info_msg ("Solving sketch for " ^ problem.loop_name);
    (* Compile the sketch to a Racket file, call Rosette, and parse the
       solution. *)
    let _racket_elapsed, parsed =
      (if !solve_incrementally then call_solver_incremental else call_solver ~timeout:(-1))
        ~inner parent_ctx problem
    in
    match parsed with
    | None ->
        Log.error_msg Fmt.(str "NO SOLUTION found for %s (solver returned unsat)." lp_name);
        if !FnPretty.skipped_non_linear_operator then (
          (* Try with non-linear operators. *)
          FnPretty.reinit expr_depth true;
          solve_one parent_ctx problem)
        else (
          FnPretty.reinit expr_depth false;
          None)
    | Some pb -> Some pb
  with Failure s ->
    solution_failed ~failure:s problem;
    None
(* A solution has been found *)
