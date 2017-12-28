open Cil
open Canalyst
open Loops
open Format
open Utils
open PpTools

let test_filename = Conf.project_dir ^"/ocamllibs/test/nested_loops.c"

let test () =
  printf "%sTEST: nested loops%s@." (color "b-blue") color_default;
  let cfile = Canalyst.parseOneFile test_filename in
  Cfg.computeFileCFG cfile;
  process_file cfile;
  let loop_infos = get_loops () in
  IH.iter
    (fun lid cl ->
       begin
         printf "%s%s-----------------%s@." (color "b-green") (color "black")
           color_default;
         pp_loop std_formatter cl
       end)
    loop_infos;
  printf "%s%sNEW IMPLEMENTATION: OK %s@." (color "b-green") (color "black")
    color_default;
