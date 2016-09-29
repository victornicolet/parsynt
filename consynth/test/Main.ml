open Cil
open Canalyst
open Format
open PpHelper
open Findloops
open Utils

module C2F = Cil2Func

(** Different test modules *)
module TC2F = TCil2Func
module TF2S = TFunc2Sketch
module TGDef = TGenDefs
module TSbx = TSymbExe

let unit_tests () =
  TSbx.test ();
  TSbx.test2 ()

let testProcessFile () =
  if Array.length Sys.argv < 2 then
    begin
      TGDef.test ();
      let loopsm = TC2F.test () in
      TF2S.test loopsm;
      eprintf "Usage : ./Main.native [test file name]\n\n";
      exit 0
    end;
  let filename = "test/"^(Array.get Sys.argv 1) in
  printf "-- test processing file -- \n";
  let loops = Canalyst.processFile filename in
  printf "-- finished --\n";
  printf "%s Functional rep. %s\n" (color "blue") default;
  IM.iter
    (fun k cl ->
       let stmt = mkBlock(cl.Cloop.new_body) in
       let igu = check_option cl.Cloop.loop_igu in
       let r, stv = cl.Cloop.rwset in
       let letn, _ = C2F.cil2func stv stmt igu in
       C2F.printlet (stv, letn))
    loops;;

unit_tests ();

testProcessFile ();;
