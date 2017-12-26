open Cil
open Findloops
open Utils
open Sketch
open Format
open PpTools

module C = Canalyst
module Cl = Cloop

let test () =
  let filename = "test/test-gendefs.c" in
  printf "%s-- test C -> Rosette definitions  -- %s\n"
    (color "red") color_default;
  let loops = C.func2sketch (C.cil2func (C.processFile filename)) in
  List.iter
    (fun srp ->  C.pp_sketch Format.std_formatter srp; print_endline "";)
    loops
