open Cil
open Loops
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
  let loops = C.processFile filename in
  IM.iter
    (fun k cl ->
      let vars = VSOps.vs_of_defsMap cl.Cl.definedInVars in
      let (r, rw, w) = cl.Cl.rwset in
      pp_symbolic_definitions_of std_formatter r vars
    )
    loops
