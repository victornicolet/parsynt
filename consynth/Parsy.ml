open Local
open Str
open Format
open PpHelper
open Utils

module C = Canalyst


let solve_sketch sketch =
  let fd_ic, fd_oc = Unix.pipe () in
  let ic, oc =
    Unix.in_channel_of_descr fd_ic,
    Unix.out_channel_of_descr fd_oc
  in
  let custom_fmt = make_formatter (Pervasives.output_substring oc)
    (fun () -> flush oc) in
  C.pp_sketch custom_fmt sketch;
  Local.from_input ic


let main () =
  if Array.length Sys.argv < 2 then
    begin
      eprintf "%sUsage : ./Parsy.native [filename]%s" (color "red") default;
      exit 0;
    end;
  let filename = Array.get Sys.argv 1 in
  let sketch_map = C.func2sketch (C.cil2func (C.processFile filename)) in
  IM.iter
    (fun k sketch -> solve_sketch sketch)
    sketch_map ;;

main ();
