open Cil
open Canalyst
open Printf

let testProcessFile =
  printf "-- test processing file -- \n";
  Canalyst.processFile "test/test.c"

