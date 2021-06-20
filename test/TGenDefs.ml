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
open Loops
open Utils
open Sketch
open Format
open PpTools
module C = Canalyst

let test () =
  let filename = "test/test-gendefs.c" in
  printf "%s-- test C -> Rosette definitions  -- %s\n" (color "red") color_default;
  let cfile, loops = C.processFile filename in
  let loops = C.func2sketch cfile (C.cil2func cfile loops) in
  List.iter
    (fun srp ->
      C.pp_sketch Config.rosette Format.std_formatter srp;
      print_endline "")
    loops
