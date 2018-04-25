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

open Cil
open Conf
open Str
open Format
open Utils
open Utils.PpTools
open Getopt
open FuncTypes
open InnerFuncs

open FpExact


module L = Local
module C = Canalyst
module Pf = Proofs


let debug = ref false
let verbose = ref false
let elapsed_time = ref 0.0
let skip_first_solve = ref false
let synthTimes = (Conf.get_conf_string "synth_times_log")
let use_z3 = ref false
let exact_fp = ref false

let options = [
  ( 'd', "dump",  (set Local.dump_sketch true), None);
  ( 'e', "exact-fp", (set exact_fp true), None);
  ( 'f', "debug-func", (set Cil2Func.debug true), None);
  ( 'g', "debug", (set debug true), None);
  ( 'k', "kill-first-solve", (set skip_first_solve true), None);
  ( 'o', "output-folder", None,
      Some (fun o_folder -> Conf.output_dir := o_folder));
  ( 's', "debug-sketch", (set Sketch.debug true), None);
  ( 'v', "verbose", (set verbose true), None);
  ( 'x', "debug-variable-discovery", (set VariableDiscovery.debug true), None);
  ( 'z', "use-z3", (set use_z3 true), None)]


let solution_failed ?(failure = "") problem =
  printf "@.%sFAILED:%s Couldn't retrieve the solution from the parsed ast\
          of the solved problem of %s.@."
    (color "red") color_default problem.loop_name;
  if failure = "" then ()
  else
    printf "Failure: %s" failure


let solution_found racket_elapsed lp_name parsed (problem : prob_rep) =
  if !verbose then
    printf "@.%sSOLUTION for %s %s:@.%a"
      (color "green") lp_name color_default RAst.pp_expr_list parsed;
  (* Open and append to stats *)
  let oc = open_out_gen [Open_wronly; Open_append; Open_creat; Open_text]
      0o666 synthTimes in
  Printf.fprintf oc "%s,%.3f\n" lp_name racket_elapsed;
  let sol_info =
    try
      Codegen.get_solved_sketch_info parsed
    with _ ->
      (solution_failed problem;
       failwith "Couldn't retrieve solution from parsed ast.")
  in
  (** Simplify the solution using Z3 *)
  let translated_join_body =
    init_scm_translate
      problem.scontext.all_vars problem.scontext.state_vars;
    match scm_to_fn sol_info.Codegen.join_body with
    | Some sklet, _ ->
      if !use_z3 then
        (* (try *)
        (*    let z3t = new Z3c.z3Translator sketch.scontext.all_vars in *)
        (*    (z3t#simplify_let c_style_solution) *)
        (*  with Failure s -> *)
        (*    (eprintf "@\nFAILURE : couldn't simplify join using Z3.@\n"; *)
        (*     eprintf "MESSAGE: %s@\n" s; *)
        (*     c_style_solution)) *)
        print_endline "Z3 expression simplifcation in progress";
        sklet

    | None, Some expr ->
      (eprintf "Failed in translation, we got an expression %a for the join."
         FPretty.pp_fnexpr expr;
       failwith "Failed to translate the solution in a function in our\
                 intermediate representation.")

    | _ ->
      failwith "Failed to translate the solution in our \
                intermediate representation."
  in
  init_scm_translate problem.scontext.all_vars problem.scontext.state_vars;
  let remap_init_values maybe_expr_list =
    match maybe_expr_list with
    | Some expr_list ->
      List.fold_left2
        (fun map vid ast_expr ->
           IM.add vid ast_expr map)
        IM.empty
        (VarSet.vids_of_vs problem.scontext.state_vars) expr_list

    | None ->
      (** If auxiliaries have been created, the sketch has been solved
          without having to assign them a specific value. We can
          just create placeholders according to their type. *)
      IH.fold
        (fun vid vi map ->
           IM.add vid
             (match vi.vtype with
              | Integer -> RAst.Int_e 0
              | Boolean -> RAst.Bool_e true
              | Real -> RAst.Int_e 1
              | _ -> RAst.Nil_e) map)
        Sketch.Join.auxiliary_variables IM.empty
  in
  {problem with
   join_solution =
     ExpressionReduction.normalize problem.scontext translated_join_body;
   init_values = remap_init_values sol_info.Codegen.init_values}


let rec solve_one ?(inner=false) ?(solver = Conf.rosette) ?(expr_depth = 1) problem =
  (* Set the expression depth of the sketch printer. *)
  FPretty.holes_expr_depth := expr_depth;
  let lp_name = problem.loop_name in
  try
    if !verbose then
      (printf "@.%sSOLVING %s.%s@." (color "blue") lp_name color_default;
       printf "Sketch: %a@." FPretty.pp_fnexpr problem.join_body);
    let racket_elapsed, parsed =
      L.compile_and_fetch solver
        ~print_err_msg:Racket.err_handler_sketch (C.pp_sketch solver) problem
    in
    if List.exists (fun e -> (RAst.Str_e "unsat") = e) parsed then
      (* We get an "unsat" answer : add loop to auxliary discovery *)
      begin
        printf
          "@.%sNO SOLUTION%s found for %s (solver returned unsat)."
          (color "orange") color_default lp_name;
        if !FPretty.skipped_non_linear_operator then
          (** Try with non-linear operators. *)
          (FPretty.reinit ~ed:expr_depth ~use_nl:true;
           solve_one problem)
        else
          (FPretty.reinit ~ed:expr_depth ~use_nl:false;
           None)
      end
    else
      (* A solution has been found *)
      begin
        try
          Some (solution_found racket_elapsed lp_name parsed problem)
        with Failure s ->
          solution_failed ~failure:s problem;
          None
      end
  with Failure s ->
    begin
      solution_failed ~failure:s problem;
      None
    end


(**
   Recursively solve the inner loops using different tactics.
   @param problem The problem we are currently trying to solve.
   @return Some problem if all the inner functions can be paralleized or
   made memoryless. None if not.
*)
let rec solve_inners problem =
  if List.length problem.inner_functions = 0 then
    Some problem
  else
    let solve_inner_problem problem = solve_one ~inner:true problem in
    (* Solve the inner functions. *)
    let inner_funcs =
      somes (List.map solve_inner_problem problem.inner_functions)
    in
    (* Replace occurrences of the inner functions by join operator and new
       input sequence if possible.
       - Condition 1: all inner function are solved. *)
    if List.length inner_funcs = List.length problem.inner_functions then
      Some (replace_by_join problem inner_funcs)
    else
      None


and solve_problem problem =
  (* Try to solve the inner loops first *)
  let aux_solve problem =
      let tactic1_sol =
        if !skip_first_solve then None else solve_one problem
      in
      match tactic1_sol with
      | Some x -> Some x
      | None ->
        printf "Searching auxiliaries for %s ...@." problem.loop_name;
        let problem =
          Canalyst.find_new_variables problem
        in
        match solve_one problem with
        | Some x -> Some x
        | None -> solve_one ~expr_depth:2 problem
        (** If the problem is not solved yet, might be because expression
            depth is too limited *)
  in
  maybe_apply aux_solve (solve_inners problem)


(** --------------------------------------------------------------------------*)
(** Generating a TBB implementation of the parallel solution discovered *)
let output_tbb_tests (solutions : prob_rep list) =
  let tbb_test_filename (solution : prob_rep) =
    let folder_name =
      (!Conf.output_dir)^"/"^(Conf.get_conf_string "tbb_examples_folder")
    in
    let errco =
      if Sys.file_exists folder_name then
        0
      else
        Sys.command ("mkdir "^folder_name)
    in
    if errco = 0 then
      folder_name^(Tbb.pbname_of_sketch solution)^".cpp"
    else
      failwith "Failed to create directory for tbb example output."
  in
  printf "@.%s%sGenerating implementations for solved examples..%s@."
    (color "black") (color "b-green") color_default;
  List.iter (Tbb.output_tbb_test tbb_test_filename) solutions


(** Generating Dafny proofs *)
let output_dafny_proofs (sols : prob_rep list) : unit =
  let dafny_proof_filename (sol : prob_rep) =
    let folder_name =
      (!Conf.output_dir)^"/"^(Conf.get_conf_string "dafny_examples_folder")
    in
    let errco =
      if Sys.file_exists folder_name then
        0
      else
        Sys.command ("mkdir "^folder_name)
    in
    if errco = 0 then
      folder_name^(Pf.filename_of_solution sol)^".dfy"
    else
      failwith "Failed to create directory for Dafny proof output."

  in
  printf "@.%s%sGenerating proofs for solved examples..%s@."
    (color "black") (color "b-green") color_default;
  List.iter (Pf.output_dafny_proof dafny_proof_filename) sols

(** --------------------------------------------------------------------------*)

let main () =
  parse_cmdline options print_endline;
  if Array.length Sys.argv < 2 then
    begin
      eprintf "%sUsage : ./Parsy.native [filename] .. options%s@."
        (color "red") color_default;
      flush_all ();
      exit 1;
    end;
  L.debug := !debug;
  let filename = Array.get Sys.argv 1 in

  if !debug then
    begin
      FError.logfile := "log"^(string_of_float (Sys.time ()))^filename;
      printf "Logging in %s@." !FError.logfile;
      (** Set all the debug flags to true *)
      Cil2Func.debug := true;
      Sketch.debug := true;
      Sketch.Body.debug := true;
      Sketch.Join.debug := true;
      VariableDiscovery.debug := true;
    end;

  if !verbose then
    begin
      Loops.verbose := true;
      Canalyst.verbose := true;
    end;

  elapsed_time := Unix.gettimeofday ();
  printf "Parsing C program ...\t\t\t\t";
  let c_file, loops = C.processFile filename in
  printf "%sDONE%s@.@.%sC program -> partial functional representation ...%s\t"
    (color "green") color_default (color "yellow") color_default;
  let functions = C.cil2func c_file loops in
  printf "%sDONE%s@.@.%sPartial functional representation -> functional representation ...%s\t\t"
    (color "green") color_default (color "yellow") color_default;
  let problem_list = Canalyst.func2sketch c_file functions in
  printf "%sDONE%s@.@.%sSolving sketches ...%s\t\t@." (color "green") color_default (color "yellow") color_default;
  (** Try to solve the sketches without adding auxiliary variables *)
  (* All the sketches that have been solved, including with auxiliaries *)
  let solved =
    List.map check_option
      (List.filter is_some
         (List.map solve_problem problem_list))
  in
  (** Handle all the solutions found *)
  (List.iter (fun problem -> FPretty.pp_problem_rep std_formatter problem)
     (somes solved));
  (* For each solved problem, generate a TBB implementation *)
  output_tbb_tests (somes solved);
  (* If exact_fp is set, generate the exact floating point parallel
     implementation *)
  if !exact_fp then (List.iter fpexp_header (somes solved));
  (* Generate a proof in Dafny. *)
  output_dafny_proofs (somes solved);
  (* Total elapsed_time  *)
  elapsed_time := (Unix.gettimeofday ()) -. !elapsed_time;
  printf "@.\t\t\t\t\t\t%sFINISHED in %.3f s%s@.@." (color "green")
    !elapsed_time color_default;;

main ();
