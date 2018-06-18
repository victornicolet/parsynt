(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
  *)

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
module TGDef = TGenDefs
module TSbx = TSymbExe
module TScm = TestSchemeParsing
module TSl = TestSynthlib
module TNL = TNestedLoops
module TE = TExpressions
module TVd = TDiscovery;;
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
  ( 'w', "debug-symbex", (set SymbExe.debug true), None);
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
       let _ = C2F.cil2func [] cl.lvariables stmt igu in
       ())
    loops;;


parse_cmdline options print_endline;

match !tid with
| 0 -> ignore(TC2F.test ())
| 1 -> testProcessFile ()
| 2 -> TNL.test ()
| 3 -> TSl.test ()
| 4 -> TVd.test ()
| 5 -> TE.test ()
| 6 -> TSbx.test ()
| 7 ->
  TE.test ();
  TSbx.test ();
  TVd.test ()
| _ -> ()
