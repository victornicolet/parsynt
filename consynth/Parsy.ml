open Local
open Str
open Format
open PpHelper
open Utils

module C = Canalyst

let debug = ref true
let elapsed_time = ref 0.

let main () =
  if Array.length Sys.argv < 2 then
    begin
      eprintf "%sUsage : ./Parsy.native [filename]%s@." (color "red") default;
      flush_all ();
      exit 1;
    end;
  Local.debug := !debug;
  let filename = Array.get Sys.argv 1 in
  if Array.length Sys.argv > 2 then
    begin
      match Array.get Sys.argv 2 with
      | "--dump-sketch" ->
         Local.dump_sketch := true
      | _ -> ()
    end;
  elapsed_time := Unix.gettimeofday ();
  printf "Compiling sketches ...\t\t";
  let sketch_map = C.func2sketch (C.cil2func (C.processFile filename)) in
  printf "%sDONE%s@.@.Solving sketches ...\t\t" (color "green") default;
  List.iter
    (fun sketch -> compile_and_fetch sketch)
    sketch_map;
  elapsed_time := (Unix.gettimeofday ()) -. !elapsed_time;
  printf "%sFINISHED in %.3f s%s@." (color "green") !elapsed_time default;;

main ();
