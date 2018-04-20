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
open Loops
open Format
open Utils
open PpTools
open InnerFuncs
open FuncTypes

let test_filenames = glob (Conf.project_dir ^"/test/nested_loops/*.c")

let test_verbosity = ref 1

let trynf e m =
  try e with Not_found -> failhere __FILE__ "test" m

let one_test test_filename =
  Canalyst.clear ();
  printf "@.%s%sTEST: nested loops : %s %s@." (color "b-yellow") (color "black")
    test_filename color_default;
  let cfile = trynf (Canalyst.parseOneFile test_filename) "parseOneFile" in
  trynf (Cfg.computeFileCFG cfile) "computeCFGInfo";
  trynf (process_file cfile) "processFile";
  let loop_infos = trynf (get_loops ()) "get_loops" in
  if !test_verbosity > 2 then
    IH.iter
      (fun lid cl ->
         begin
           printf "%s%s----------------%s@." (color "b-green") (color "black")
             color_default;
           try
             pp_loop std_formatter cl
           with Not_found ->
             failhere __FILE__ "test" "pp_loop"
         end)
      loop_infos;

  (* Cil2Func.debug := true; *)
  IHTools.add_all Cil2Func.global_loops loop_infos;
  let func_infos = Canalyst.cil2func cfile (IM.of_ih loop_infos) in
  (* Print the intermediary functional wrapping of the program. *)
  if !test_verbosity > 2 then
    List.iter
      (fun (finfo : func_info) ->
         let printer = new Cil2Func.cil2func_printer finfo.lvariables in
         printer#fprintlet std_formatter finfo.func
      ) func_infos;

  if !test_verbosity > 0 then
    printf "@.CIL --> FUNC translation: OK@.";
  let unsolved_sketches = Canalyst.func2sketch cfile func_infos in

  if !test_verbosity > 0 then
    List.iter (FPretty.pp_problem_rep std_formatter) unsolved_sketches;

  if !test_verbosity > 0 then
    printf "@.FUNC --> FUNC translation: OK@.";

  let transformed_inner =
    List.map (fun pb -> replace_by_join pb pb.inner_functions) unsolved_sketches
  in
  if !test_verbosity > 0 then
    List.iter (FPretty.pp_problem_rep std_formatter) transformed_inner


let test () =
  List.iter (fun tfname -> one_test tfname) test_filenames
