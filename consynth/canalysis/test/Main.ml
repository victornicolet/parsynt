open Cil
open Canalyst
open Format
open Prefunc

module LF = Loops2ssa.Floop

let testProcessFile () =
  if Array.length Sys.argv < 2 then
    begin
      eprintf "Usage : ./Main.native [test file name]\n\n";
      exit 0
    end;
  let filename = "test/"^(Array.get Sys.argv 1) in
  printf "-- test processing file -- \n";
  ignore(Canalyst.processFile filename);
  printf "-- finished --\n";;


testProcessFile ()
