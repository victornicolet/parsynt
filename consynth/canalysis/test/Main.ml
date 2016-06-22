open Cil
open Canalyst
open Printf
open Prefunc

module LF = Loops2ssa.Floop

let testProcessFile () =
  printf "-- test processing file -- \n";
  let loops = Canalyst.processFile "test/test.c" in
  Inthash.iter (fun i cl ->
    printf "\n\n Loop %i " cl.LF.sid;
    Inthash.iter
    (fun i pf -> 
      printf "\n%i = %s" i
        (string_of_prefunc pf))
      cl.LF.body )
    loops;;

testProcessFile ()
