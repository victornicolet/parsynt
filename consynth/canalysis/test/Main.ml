open Cil
open Canalyst
open Format
open PpHelper
open Loops
open Utils

module C2F = Cil2Func
module LF = Loops2ssa.Floop

module T1 = TCil2Func

let testProcessFile () =
  if Array.length Sys.argv < 2 then
    begin
      T1.test ();
      eprintf "Usage : ./Main.native [test file name]\n\n";
      exit 0
    end;
  let filename = "test/"^(Array.get Sys.argv 1) in
  printf "-- test processing file -- \n";
  ignore(Canalyst.processFile filename);
  printf "-- finished --\n";
  printf "%s Functional rep. %s\n" (color "blue") default;
  let loops = Canalyst.getLoops () in
  IH.iter
    (fun k cl ->
      let stmt = mkBlock(cl.Cloop.statements) in
      let stateVars = ListTools.outer_join_lists
	    (match cl.Cloop.rwset with (r, w, rw) -> w, rw) in
      let vars = VSOps.vs_of_defsMap cl.Cloop.definedInVars in
      let stv = VSOps.subset_of_list stateVars vars in
      C2F.printlet (C2F.cil2func stmt stv))
    loops;;


testProcessFile ()
