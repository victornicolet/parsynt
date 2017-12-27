open Cil
open Canalyst
open Findloops
open Format
open Utils
open PpTools
open Cloop

let test_filename = Conf.project_dir ^"/ocamllibs/test/nested_loops.c"

let test () =
  printf "%sTEST: nested loops%s@." (color "b-blue") color_default;
  let cfile = Canalyst.parseOneFile test_filename in
  Cfg.computeFileCFG cfile;
  let loops, lids = Findloops.processFile cfile in
  IM.iter
    (fun lid cl ->
       begin
         printf "%s%s-----------------%s@." (color "b-green") (color "black")
           color_default;
         printf "%s@." (Cloop.__str__ cl);
         if List.length cl.inner_loops > 0 then
           printf "Has inner loops.@."
         else
           printf "No inner loop.@.";
         printf "%sOld loop body:%s@." (color "yellow") color_default;
         CilTools.ppbk (old_body cl);
         printf "%sNew loop body:%s@." (color "yellow") color_default;
         CilTools.ppbk (new_body cl);
       end)
    loops;
  printf "%s%s OK %s@." (color "b-green") (color "black") color_default;
