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

  Cil2Func.debug := true;
  IHTools.add_all Cil2Func.global_loops loop_infos;
  let func_infos = Canalyst.cil2func cfile (IM.of_ih loop_infos) in
  List.iter
    (fun (finfo : func_info) ->
       let printer = new Cil2Func.cil2func_printer finfo.lvariables in
       printer#fprintlet std_formatter finfo.func
    ) func_infos;
  printf "@.%s%sCIL --> FUNC translation: OK %s@." (color "b-green")
    (color "black")
    color_default;

  let unsolved_sketches = Canalyst.func2sketch cfile func_infos in

  List.iter (FPretty.pp_problem_rep std_formatter) unsolved_sketches;

  printf "@.%s%sFUNC --> FUNC translation: OK %s@." (color "b-green")
    (color "black")
    color_default;
