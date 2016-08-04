open Cil
open Findloops
open Utils
open Sketch
open Format
open PpHelper

module C = Canalyst
module Cl = Cloop

let test () =
  let filename = "test/test-gendefs.c" in
  printf "%s-- test C -> Rosette definitions  -- %s\n"
    (color "red") default;
  let loops = C.func2sketch (C.cil2func (C.processFile filename)) in
  IM.iter
    (fun k (rv, state, all_v, loop_b, join_b, rcs) ->
      pp_rosette_sketch std_formatter (rv, state, all_v, loop_b, join_b, rcs);
      print_endline "";
    )
    loops
