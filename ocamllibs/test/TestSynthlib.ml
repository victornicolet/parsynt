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

open Conf
open Cil
open Format
open FuncTypes
open Synthlib
open Synthlib2ast
open Utils.ListTools
open Utils.PpTools
open TestUtils
open FuncTypes2Synthlib

let on_input input =
  printf "%sInput: %s%s@." (color "green") input color_default;
  try
    let _ =
      parsechan (open_in (project_dir^"/ocamllibs/test/synthlib/"^input))
    in
    printf "%s%sOK%s@." (color "black") (color "b-green") color_default
  with Syparser.Error->
    print_err_std "Failed to parse input.\n"


let test_conversion () =
  printf "TEST conversion functions.@.";
  let x,y,z,ints, i =
    make_int_varinfo "x", make_int_varinfo "y", make_int_varinfo "z",
    make_int_array_varinfo "ints", make_int_varinfo "i"
  in
  let a,b,c, bools = make_bool_varinfo "a",
                     make_bool_varinfo "b",
                     make_bool_varinfo "c",
                     make_bool_array_varinfo "bools"
  in
  let e1 = (_b (_b (evar x) Times (evar y)) Plus (a $ (evar i))) in
  printsy (SyCommands
             [SyFunDefCmd("dummy", [("x", SyIntSort)], SyIntSort, to_term e1)])




let test_gen_arity_defs () =
  printf "TEST gen_arity_defs@.";
  let deffs =
    List.map
      (fun (a,b) -> b)
      (gen_arity_defs
         ("fsum", SyIntSort)
         ("sum", SyIntSort, SyApp("+",[SyId "a"; SyId"sum"]))
         [("sum",SyIntSort)]
         ("a", SyIntSort))
  in
  Synthlib.printsy (SyCommandsWithLogic (SyLIA, deffs));
    let deffs =
    List.map
      (fun (a,b) -> b)
      (gen_arity_defs
         ("fmts", SyIntSort)
         ("mts", SyIntSort, SyApp("max",
                                  [SyApp("+", [SyId "a"; SyId"mts"]);
                                   SyLiteral (SyInt 0)]))
         [("mts",SyIntSort)]
         ("a", SyIntSort))
  in
  Synthlib.printsy (SyCommandsWithLogic (SyLIA, deffs))




let test () =
  printf "%s********* TESTING SYNTHLIB2 PARSER **********%s@."
    (color "b-blue")
    color_default;
  let children = Sys.readdir (Conf.project_dir^"/ocamllibs/test/synthlib/") in
  let filter s = (not (String.contains s '~'))
                 && (not (String.contains s '*'))
                 && (not (String.contains s '#')) in
  Array.iter  (fun s -> if filter s then on_input s) children;
  test_gen_arity_defs ();
  test_conversion ()
