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

let test_filename = Conf.project_dir ^"/test/nested_loops.c"

let trynf e m =
  try e with Not_found -> failhere __FILE__ "test" m

let test () =
  printf "%sTEST: nested loops%s@." (color "b-blue") color_default;
  let cfile = trynf (Canalyst.parseOneFile test_filename) "parseOneFile" in
  trynf (Cfg.computeFileCFG cfile) "computeCFGInfo";
  trynf (process_file cfile) "processFile";
  let loop_infos = trynf (get_loops ()) "get_loops" in
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

  Cil2Func.debug := true;
  IHTools.add_all Cil2Func.global_loops loop_infos;
  let func_infos = Canalyst.cil2func cfile (IM.of_ih loop_infos) in
  List.iter
    (fun (finfo : func_info) ->
       let printer = new Cil2Func.cil2func_printer finfo.lvariables in
       printer#fprintlet std_formatter finfo.func
    ) func_infos;
  printf "@.%s%sCIL --> FUNC translation: OK %s@." (color "b-green")
    (color "black")
    color_default;

  let unsolved_sketches = Canalyst.func2sketch cfile func_infos in

  List.iter (FPretty.pp_problem_rep std_formatter) unsolved_sketches;

  printf "@.%s%sFUNC --> FUNC translation: OK %s@." (color "b-green")
    (color "black")
    color_default;

  let transformed_inner =
    List.map (fun pb -> replace_by_join pb pb.inner_functions) unsolved_sketches
  in

    List.iter (FPretty.pp_problem_rep std_formatter) transformed_inner;
