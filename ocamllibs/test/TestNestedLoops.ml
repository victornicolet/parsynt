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
  Cil2Func.debug := true;
  let func_infos = Canalyst.cil2func cfile (IM.of_ih loop_infos) in
  List.iter
    (fun (finfo : func_info) ->
       let printer = new Cil2Func.cil2func_printer finfo.lvariables in
       printer#fprintlet std_formatter finfo.func
    ) func_infos;
  let unsolved_sketches = Canalyst.func2sketch cfile func_infos in
  List.iter (FPretty.pp_problem_rep std_formatter) unsolved_sketches;
