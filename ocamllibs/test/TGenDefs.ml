open Cil
open Loops
open Utils
open Sketch
open Format
open PpTools

module C = Canalyst

let test () =
  let filename = "test/test-gendefs.c" in
  printf "%s-- test C -> Rosette definitions  -- %s\n"
    (color "red") color_default;
  let cfile, loops = C.processFile filename in
  let loops = C.func2sketch cfile (C.cil2func cfile loops) in
  List.iter
    (fun srp ->  C.pp_sketch Format.std_formatter srp; print_endline "";)
    loops
