open Str
open Format
open PpHelper
open Utils
open Getopt
open SketchTypes
open Cil


module L = Local
module C = Canalyst
module Pf = Proofs

let debug = ref false
let elapsed_time = ref 0.0
let skip_first_solve = ref false

let err_handler_sketch i =
  eprintf "%sError%s while running racket on sketch.@."
    (color "red") default

let options = [
  ( 'd', "dump",  (set Local.dump_sketch true), None);
  ( 'g', "debug", (set debug true), None);
  ( 'f', "debug-func", (set Cil2Func.debug true), None);
  ( 's', "debug-sketch", (set Sketch.debug true), None);
  ( 'k', "kill-first-solve", (set skip_first_solve true), None);
  ( 'v', "debug-variable-discovery", (set VariableDiscovery.debug true), None);
  ( 'o', "output-folder", None,
    Some (fun o_folder -> Conf.output_dir := o_folder))]

let solution_found lp_name parsed (sketch : sketch_rep) solved =
  printf "@.%sSOLUTION for %s %s:@.%a"
    (color "green") lp_name default Ast.pp_expr_list parsed;
  let sol_info =
    try
      Codegen.get_solved_sketch_info parsed
    with _ ->
      (printf "@.%sFAILED:%s Couldn't retrieve the solution from the parsed ast\
               of the solved sketch of %s.@."
         (color "red") default sketch.loop_name;
       failwith "Couldn't retrieve solution from parsed ast.")
  in
  (** Simplify the solution using Z3 *)
  (* let z3t = new Z3c.z3Translator sketch.scontext.all_vars in *)
  let translated_join_body =
    SketchTypes.init_scm_translate
      sketch.scontext.all_vars sketch.scontext.state_vars;
    match scm_to_sk sol_info.Codegen.join_body with
    | Some sklet, _ ->
      (* (try (z3t#simplify_let c_style_solution) *)
      (*  with Failure s -> *)
      (*    (eprintf "@\nFAILURE : couldn't simplify join using Z3.@\n"; *)
      (*     eprintf "MESSAGE: %s@\n" s; *)
      (*     c_style_solution)) *)
      sklet

    | None, Some expr ->
      (eprintf "Failed in translation, we got an expression %a for the join."
         SPretty.pp_skexpr expr;
       failwith "Failed to translate the solution in a function in our\
                 intermediate representation.")

    | _ ->
      failwith "Failed to translate the solution in our \
                intermediate representation."
  in
  init_scm_translate sketch.scontext.all_vars sketch.scontext.state_vars;
  let remap_init_values maybe_expr_list =
    match maybe_expr_list with
    | Some expr_list ->
      List.fold_left2
        (fun map vid ast_expr ->
           IM.add vid ast_expr map)
        IM.empty
        (VSOps.vids_of_vs sketch.scontext.state_vars) expr_list
    | None ->
      (** If auxliaries have been created, the sketch has been solved
          without having to assign them a specific value. We can
          just create placeholders according to their type. *)
      IH.fold
        (fun vid vi map ->
           IM.add vid
             (match type_of_ciltyp vi.vtype with
              | Integer -> Ast.Int_e 0
              | Boolean -> Ast.Bool_e true
              | Real -> Ast.Int_e 1
              | _ -> Ast.Nil_e) map)
        Sketch.Join.auxiliary_variables IM.empty
  in
  {sketch with
   join_solution =
     ExpressionReduction.simplify_reduce translated_join_body sketch.scontext;
   init_values = remap_init_values sol_info.Codegen.init_values}::solved

let solve ?(expr_depth = 1) (sketch_list : sketch_rep list) =
  SPretty.holes_expr_depth := expr_depth;
  let rec solve_one (solved, unsolved) sketch =
    let lp_name = sketch.loop_name in
    try
      printf "@.SOLVING sketch for %s.@." lp_name;
      let parsed =
        L.compile_and_fetch
          ~print_err_msg:err_handler_sketch C.pp_sketch sketch
      in
      if List.exists (fun e -> (Ast.Str_e "unsat") = e) parsed then
        (* We get an "unsat" answer : add loop to auxliary discovery *)
        begin
          printf
            "@.%sNO SOLUTION%s found for %s (solver returned unsat)."
            (color "orange") default lp_name;
          if !SPretty.skipped_non_linear_operator then
            (** Try with non-linear operators. *)
            (SPretty.reinit ~ed:expr_depth ~use_nl:true;
             solve_one (solved, unsolved) sketch)
          else
            (SPretty.reinit ~ed:expr_depth ~use_nl:false;
            (solved, unsolved@[sketch]))
        end
      else
        (* A solution has been found *)
        begin
          try
            solution_found lp_name parsed sketch solved, unsolved
          with Failure s ->
            printf "@.@[%sFAILED%s :\
                    solution found, but couldn't interpret it for@\n\
                    %s%s%s.@\n\
                    %sFailure%s : %s@.@]"
              (color "red") default (color "red") lp_name default (color "red")
              default s;
            (solved, unsolved)
        end
    with Failure s ->
      begin
        printf "@.%sFAILED to find a solution for %s%s.@.Failure : %s@."
          (color "red") lp_name default s;
        (solved, unsolved)
      end
  in
  List.fold_left solve_one ([], []) sketch_list

(** Generating a TBB implementation of the parallel solution discovered *)
let tbb_test_filename (solution : sketch_rep) =
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


let output_tbb_test (solution : sketch_rep) =
  let tbb_file_oc =  open_out (tbb_test_filename solution) in
  printf "New file: %s.@." (tbb_test_filename solution);
  let tbb_file_out_fmt = Format.make_formatter
      (output tbb_file_oc) (fun () -> flush tbb_file_oc) in
  let tbb_class_summary = Tbb.make_tbb_class solution in
  Tbb.fprint_tbb_class tbb_file_out_fmt solution tbb_class_summary;
  close_out tbb_file_oc

let output_tbb_tests (solutions : sketch_rep list) =
  List.iter output_tbb_test solutions


(** Generating Dafny proofs *)
let dafny_proof_filename (sol : sketch_rep) =
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

let output_dafny_proof (solution : sketch_rep) =
  printf "New file: %s.@." (dafny_proof_filename solution);
  let dafny_file_oc = open_out (dafny_proof_filename solution) in
  let dafny_file_out_fmt =
    Format.make_formatter (output dafny_file_oc) (fun () -> flush dafny_file_oc)
  in
  Pf.gen_proof_vars solution;
  Pf.pp_all_and_clear dafny_file_out_fmt;
  fprintf dafny_file_out_fmt "@.";
  close_out dafny_file_oc

let output_dafny_proofs (sols : sketch_rep list) : unit =
  List.iter output_dafny_proof sols

(** --------------------------------------------------------------------------*)

let main () =
  parse_cmdline options print_endline;
  if Array.length Sys.argv < 2 then
    begin
      eprintf "%sUsage : ./Parsy.native [filename] .. options%s@."
        (color "red") default;
      flush_all ();
      exit 1;
    end;
  L.debug := !debug;
  let filename = Array.get Sys.argv 1 in
  if !debug = true then
    begin
      SError.logfile := "log"^(string_of_float (Sys.time ()))^filename;
      printf "Logging in %s" !SError.logfile;
      (** Set all the debug flags to true *)
      Cil2Func.debug := true;
      Sketch.debug := true;
      Sketch.Body.debug := true;
      Sketch.Join.debug := true;
      VariableDiscovery.debug := true;
    end
  else ();

  elapsed_time := Unix.gettimeofday ();
  printf "Parsing C program ...\t\t\t\t";
  let c_program = C.processFile filename in
  printf "%sDONE%s@.@.C program -> functional representation ...\t"
    (color "green") default;
  let functions = C.cil2func c_program in
  printf "%sDONE%s@.@.Functional representation -> sketch ...\t\t"
    (color "green") default;
  let sketch_list = Canalyst.func2sketch functions in
  printf "%sDONE%s@.@.Solving sketches ...\t\t@." (color "green") default;
  (** Try to solve the sketches without adding auxiliary variables *)
  let solved, unsolved =
    if !skip_first_solve then ([], sketch_list)
    else
      solve sketch_list
  in
  (** Now discover auxiliary variables *)
  if List.length unsolved > 0 then
    printf "%sDONE%s@.@.Finding auxiliary variables ...@.@."
      (color "green") default;

  let with_auxiliaries =
    List.map
      (fun sketch ->
         printf "Searching auxiliaries for %s ...@." sketch.loop_name;
         Canalyst.find_new_variables sketch)
      unsolved
  in
  let solved_with_aux, unsolved_with_aux =
    solve with_auxiliaries
  in
  (** If some sketches are not solved yet, might be because expression depth
      is too limited *)
  let solved_depth_2, unsolved_with_aux =
    if List.length unsolved_with_aux > 0 then
      solve ~expr_depth:2 unsolved_with_aux
    else [], unsolved_with_aux
  in
  let finally_solved = solved@solved_with_aux@solved_depth_2 in
  (** Handle all the solutions found *)
  (List.iter
     (fun sketch ->
        printf "@.%s%sSummary for %s (%i) :%s@.\t%sLoop body :%s@.%a@.\t%sJoin:%s@.%a@."
          (color "black") (color "b-green")
          sketch.loop_name sketch.id
          default
          (color "b") default
          SPretty.pp_sklet sketch.loop_body
          (color "b") default
          SPretty.pp_sklet sketch.join_solution;
        let fd, cbody = sklet_to_stmts sketch.host_function sketch.loop_body in
        printf "@.%s@." (CilTools.psprint80 Cil.dn_stmt cbody)


     )
     finally_solved);
  printf "@.%s%sGenerating implementations for solved examples..%s@."
    (color "black") (color "b-green") default;
  output_tbb_tests finally_solved;
    printf "@.%s%sGenerating proofs for solved examples..%s@."
    (color "black") (color "b-green") default;
  output_dafny_proofs finally_solved;

  elapsed_time := (Unix.gettimeofday ()) -. !elapsed_time;
  printf "@.\t\t\t\t\t\t%sFINISHED in %.3f s%s@.@." (color "green")
    !elapsed_time default;;

main ();
