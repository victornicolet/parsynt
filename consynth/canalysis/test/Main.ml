open Cil
open Canalyst
open Printf

module LC = Loops.Cloop

let testProcessFile =
  printf "-- test processing file -- \n";
  let loops = Canalyst.processFile "test/test.c" in
  Inthash.iter (fun i cl -> print_string (LC.string_of_cloop cl)) loops
