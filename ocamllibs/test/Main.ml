open Cil
open Canalyst
open Format
open Loops
open Utils
open Getopt
open TestUtils
open Utils.PpTools

module C2F = Cil2Func



(** Different test modules *)
module TC2F = TCil2Func
module TF2S = TFunc2Sketch
module TGDef = TGenDefs
module TSbx = TSymbExe
module TScm = TestSchemeParsing
module TNL = TestNestedLoops;;
(* module T3 = TZ3;; *)

let tid = ref (-1);;
let filename = ref ""

(* TScm.main ();; *)
(* module TDis = TDiscovery *)
(* module TExpr = TExpressions *)

let options = [
  ( 'd', "dump",  (set Local.dump_sketch true), None);
  ( 'g', "debug", (set Local.debug true), None);
  ( 'v', "debug-var", (set VariableDiscovery.debug true), None);
  ( 't', "test-id", None, Some (fun intid -> tid := (int_of_string intid)));
  ( 'f', "file", None, Some (fun fname -> filename := fname));
];;

let testProcessFile () =
  let filename = "test/"^(!filename) in
  printf "-- test processing file -- \n";
  let cfile, loops = Canalyst.processFile filename in
  printf "-- finished --\n";
  printf "%s Functional rep. %s\n" (color "blue") color_default;
  IM.iter
    (fun k cl ->
       let stmt = loop_body cl in
       let igu = check_option cl.ligu in
       let _ = C2F.cil2func cl.lvariables stmt igu in
       ())
    loops;;


parse_cmdline options print_endline;

match !tid with
| 0 -> ignore(TC2F.test ())
| 1 -> testProcessFile ()
| 2 -> TNL.test ()
| _ -> ()
