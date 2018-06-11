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
open Str
open Format
open Utils
open Utils.PpTools
open Getopt
open FuncTypes
open Solve

module L = Local
module C = Canalyst
module Pf = Proofs
module Cg = Codegen


let debug = ref false
let verbose = ref false
let elapsed_time = ref 0.0
let skip_first_solve = ref false
let skip_all_before_vardisc = ref false

let use_z3 = ref false
(* let exact_fp = ref false *)

let options = [
  ( 'd', "dump",  (set Local.dump_sketch true), None);
  (* ( 'e', "exact-fp", (set exact_fp true), None); *)
  ( 'f', "debug-func", (set Cil2Func.debug true), None);
  ( 'g', "debug", (set debug true), None);
  ( 'i', "incremental", (set Solve.solve_incrementally true), None);
  ( 'k', "kill-first-solve", (set skip_first_solve true), None);
  ( 'K', "kill-first-inner", (set skip_all_before_vardisc true), None);
  ( 'o', "output-folder", None,
      Some (fun o_folder -> Conf.output_dir := o_folder));
  ( 's', "debug-sketch", (set Sketch.debug true), None);
  ( 'v', "verbose", (set verbose true), None);
  ( 'x', "debug-variable-discovery", (ignore(set VariableDiscovery.debug true);
                                      set SymbExe.debug true), None);
  ( 'C', "concrete-sketch", (set Sketch.concrete_sketch true), None);
  ( 'z', "use-z3", (set use_z3 true), None);
  ('I', "discovery-max-iterations", None,
   Some (fun itmax -> VariableDiscovery.max_exec_no := int_of_string itmax))]


let print_inner_result problem inner_funcs () =
  List.iter
    (fun pb ->
       printf "[INFO] Inner function %s,@.\
               \tFunction:@.%a@.\
               \tJoin:@.%a@.\
               \tIdentity state:%a@."
         pb.loop_name
         FPretty.pp_fnexpr pb.main_loop_body
         FPretty.pp_fnexpr pb.memless_solution
         (ppimap FPretty.pp_constants) pb.identity_values
    )
    inner_funcs

(**
   Recursively solve the inner loops using different tactics.
   @param problem The problem we are currently trying to solve.
   @return Some problem if all the inner functions can be paralleized or
   made memoryless. None if not.
*)
let rec solve_inners (problem : prob_rep) : prob_rep option =
  if List.length problem.inner_functions = 0 then
    Some problem
  else
    let solve_inner_problem inpb =
      if is_empty_record inpb.memless_solution then
        let start = Unix.gettimeofday () in
        let maybe_solution =
          solve_one ~inner:true (Some problem.scontext) inpb
        in
        let elapsed = Unix.gettimeofday () -. start in
        message_info (fun () ->
            printf "Inner loop %s, solved in %.3f s." inpb.loop_name elapsed);
        maybe_solution
      else Some inpb
    in
    (* Solve the inner functions. *)
    message_start_subtask ("Solvinng inner loops of "^problem.loop_name);
    let inner_funcs =
      somes (List.map solve_inner_problem problem.inner_functions)
    in
    message_done ~done_what:"(inner loops)" ();
    (* Replace occurrences of the inner functions by join operator and new
       input sequence if possible.
       - Condition 1: all inner function are solved. *)
    if List.length inner_funcs = List.length problem.inner_functions then
      begin
        if !verbose then print_inner_result problem inner_funcs ();
        Some (InnerFuncs.replace_by_join problem inner_funcs)
      end
    else
      None


and solve_problem problem =
  (* Try to solve the inner loops first *)
  let aux_solve problem =
      let tactic1_sol =
        if !skip_first_solve then None else solve_one None problem
      in
      match tactic1_sol with
      | Some x -> Some x
      | None ->
        message_start_subtask ("Searching auxiliaries for "^problem.loop_name);
        let problem' =
          (try
             Canalyst.find_new_variables problem
           with VariableDiscovery.VariableDiscoveryError s as e ->
             eprintf "[ERROR] Received variable discovery errror in aux_solve of solve_problem.@.";
             eprintf "[ERROR] Skipping problem %s.@." problem.loop_name;
             message_error_task "Couldn't find auxliary variables...\n";
             raise e)
        in
        message_done ();
        match (solve_inners =>> (solve_one None)) problem' with
        | Some x -> Some x
        | None -> solve_one ~expr_depth:2 None problem'
        (** If the problem is not solved yet, might be because expression
            depth is too limited *)
  in
  maybe_apply aux_solve
    (if !skip_all_before_vardisc then Some problem else solve_inners problem)


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
      Func2Fn.debug := true;
      Sketch.Join.debug := true;
      VariableDiscovery.debug := true;
    end;

  if !verbose then
    begin
      Solve.verbose := true;
      Loops.verbose := true;
      Canalyst.verbose := true;
      InnerFuncs.verbose := true;
      Sketch.Join.verbose := true;
      VariableDiscovery.verbose := true;
      SymbExe.verbose := true;
    end;

  elapsed_time := Unix.gettimeofday ();
  message_start_task "Parsing C program ...";
  let c_file, loops = C.processFile filename in
  message_done ();
  message_start_task "Translating C Ast to partial functional ast...";
  let functions = C.cil2func c_file loops in
  message_done ();
  message_start_task "Translating input to functional representation...";
  let problem_list = Canalyst.func2sketch c_file functions in
  message_done ();
  message_start_task "Solving sketches ...";
  message_skip ();
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
  (* if !exact_fp then (List.iter fpexp_header (somes solved)); *)
  (* Generate a proof in Dafny. *)
  output_dafny_proofs (somes solved);
  (* Total elapsed_time  *)
  elapsed_time := (Unix.gettimeofday ()) -. !elapsed_time;
  printf "@.\t\t\t\t\t\t%sFINISHED in %.3f s%s@.@." (color "green")
    !elapsed_time color_default;;

main ();
