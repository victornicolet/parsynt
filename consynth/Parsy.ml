open Str
open Format
open PpHelper
open Utils
open Getopt

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
  let unsolved =
    if !skip_first_solve then sketch_list
    else
      List.fold_left
        (fun for_discovery sketch ->
           let lp_name = sketch.C.loop_name in
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
                 for_discovery@[sketch]
               end
             else
               (* A solution has been found *)
               begin
                 printf "@.%sSOLUTION for %s %s:@.%a"
                   (color "green") lp_name default Ast.pp_expr_list parsed;
                 for_discovery
               end
           with Failure s ->
             begin
               printf "@.%sFAILED to find a solution for %s%s.@."
                 (color "red") lp_name default;
               for_discovery
             end)
        []
        sketch_list
  in

  (** Now discover auxiliary variables *)

  if List.length unsolved > 0 then
    printf "%sDONE%s@.@.Finding auxiliary variables ...@.@."
      (color "green") default;

  let with_auxiliaries =
    List.map
      (fun sketch ->
         printf "Searching auxiliaries for %s ...@." sketch.C.loop_name;
         Canalyst.find_new_variables sketch)
      unsolved
  in
  List.iter
    (fun sketch ->
       let name = sketch.C.loop_name in
       try
         printf "@.SOLVING sketch for %s.@." name;
         let parsed =
           L.compile_and_fetch
             ~print_err_msg:err_handler_sketch C.pp_sketch sketch
         in
         if List.exists (fun e -> (Ast.Str_e "unsat") = e) parsed then
           (* We get an "unsat" answer : add loop to auxliary discovery *)
           printf
             "@.%sNO SOLUTION%s found for %s with discovered variables.@."
             (color "orange") default name
         else
           (* A solution has been found *)
           printf "@.%sSOLUTION for %s %s:@.%a"
             (color "green") name default Ast.pp_expr_list parsed;

       with Failure s ->
         printf "@.%sFAILED to find a solution for %s%s.@."
           (color "red") name default)
    with_auxiliaries;

  elapsed_time := (Unix.gettimeofday ()) -. !elapsed_time;
  printf "@.\t\t\t\t\t\t%sFINISHED in %.3f s%s@.@." (color "green")
    !elapsed_time default;;

main ();
