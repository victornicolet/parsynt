open Str
open Format
open PpHelper
open Utils
open Getopt
open SketchTypes
open Cil

module L = Local
module C = Canalyst


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
  ( 'v', "debug-variable-discovery", (set VariableDiscovery.debug true), None)
]

let solution_found lp_name parsed (sketch : sketch_rep) solved =
    printf "@.%sSOLUTION for %s %s:@.%a"
      (color "green") lp_name default Ast.pp_expr_list parsed;
    let sol_info = Codegen.get_solved_sketch_info parsed in
    init_scm_translate sketch.scontext.all_vars sketch.scontext.state_vars;
    let sk_sklet_sol, sk_skexpr_sol =
      try
        scm_to_sk sol_info.Codegen.join_body
      with Failure s ->
        (printf "Failure : %s@." s; None, None)
    in
    (match sk_skexpr_sol, sk_sklet_sol with
    | Some skexpr, None ->
      printf "Expression %a@." SPretty.pp_c_expr skexpr
    | None, Some sklet ->
      printf "Let expression@. %a@." SPretty.pp_c_sklet (sk_for_c sklet)
    | _ ->
      printf "Solution not translated@.");
    {sketch with
     join_solution = sol_info.Codegen.join_body;
     init_values = sol_info.Codegen.init_values} :: solved


(** Generating a TBB implementation of the parallel solution discovered *)
let tbb_test_filename (solution : sketch_rep) =
  (Tbb.pbname_of_sketch solution)^".cpp"

let output_tbb_test (solution : sketch_rep) =
  let tbb_file_oc =  open_out (tbb_test_filename solution) in
  let tbb_file_out_fmt = Format.make_formatter
      (output tbb_file_oc) (fun () -> flush tbb_file_oc) in
  let tbb_class_summary = Tbb.make_tbb_class solution in
  Tbb.fprint_tbb_class tbb_file_out_fmt solution tbb_class_summary;
  close_out tbb_file_oc

let output_tbb_tests (solutions : sketch_rep list) =
  List.iter output_tbb_test solutions


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
      Cil2Func.debug := true;
      Sketch.debug := true;
      Sketch.Body.debug := true;
      Sketch.Join.debug := true;
      VariableDiscovery.debug := true;
    end
  else ();
    (** Set all the debug flags to true *)


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
      List.fold_left
        (fun (solved, for_discovery) sketch ->
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
                   "@.%sNO SOLUTION%s found for %s with user-defined variables."
                   (color "orange") default lp_name;
                 (solved, for_discovery@[sketch])
               end
             else
               (* A solution has been found *)
               solution_found lp_name parsed sketch solved, for_discovery
           with Failure s ->
             begin
               printf "@.%sFAILED to find a solution for %s%s.@."
                 (color "red") lp_name default;
               (solved, for_discovery)
             end)
        ([], [])
        sketch_list
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
  let finally_solved =
    List.fold_left
      (fun new_solved sketch ->
         let name = sketch.loop_name in
         try
           printf "@.SOLVING sketch for %s.@." name;
           let parsed =
             L.compile_and_fetch
               ~print_err_msg:err_handler_sketch C.pp_sketch sketch
           in
           if List.exists (fun e -> (Ast.Str_e "unsat") = e) parsed then
             (* We get an "unsat" answer : add loop to auxliary discovery *)
             (printf
                "@.%sNO SOLUTION%s found for %s with discovered variables.@."
                (color "orange") default name;
              new_solved)
           else
             (* A solution has been found *)
             solution_found name parsed sketch new_solved
         with Failure s ->
           (printf "@.%sFAILED to find a solution for %s%s.@."
              (color "red") name default);
           new_solved)
      solved
      with_auxiliaries
  in

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
          Ast.pp_expr sketch.join_solution;
        let fd, cbody = sklet_to_stmts sketch.host_function sketch.loop_body in
        printf "@.%s@." (CilTools.psprint80 Cil.dn_stmt cbody)


     )
  finally_solved);
  output_tbb_tests finally_solved;


  elapsed_time := (Unix.gettimeofday ()) -. !elapsed_time;
  printf "@.\t\t\t\t\t\t%sFINISHED in %.3f s%s@.@." (color "green")
    !elapsed_time default;;

main ();
