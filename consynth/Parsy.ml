open Str
open Format
open PpHelper
open Utils
open Getopt

module L = Local
module C = Canalyst

let debug = ref true
let elapsed_time = ref 0.0

let err_handler_sketch i =
  eprintf "%sError%s while running racket on sketch.@."
    (color "red") default

let options = [
  ( 'd', "dump",  (set Local.dump_sketch true), None);
]

let main () =
  parse_cmdline options print_endline;
  if Array.length Sys.argv < 2 then
    begin
      eprintf "%sUsage : ./Parsy.native [filename] .. options%s@."
        (color "red") default;
      flush_all ();
      exit 1;
    end;
  L.debug := !debug;
  let filename = Array.get Sys.argv 1 in
  if Array.length Sys.argv > 2 then
    begin
      match Array.get Sys.argv 2 with
      | "--dump-sketch" ->
        L.dump_sketch := true
      | _ -> ()
    end;
  elapsed_time := Unix.gettimeofday ();
  printf "Compiling sketches ...\t\t";
  let sketch_map = C.func2sketch (C.cil2func (C.processFile filename)) in
  printf "%sDONE%s@.@.Solving sketches ...\t\t@." (color "green") default;
  List.iter
    (fun sketch ->
       let parsed =
         L.compile_and_fetch
           ~print_err_msg:err_handler_sketch C.pp_sketch sketch
       in Ast.pp_expr_list std_formatter parsed)
    sketch_map;
  elapsed_time := (Unix.gettimeofday ()) -. !elapsed_time;
  printf "@.%sFINISHED in %.3f s%s@." (color "green") !elapsed_time default;;

main ();
