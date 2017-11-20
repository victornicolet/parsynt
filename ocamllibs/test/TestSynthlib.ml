open Conf
open Format
open Synthlib
open Utils.PpTools;;

printf "%s********* TESTING SYNTHLIB2 PARSER **********%s@." (color "b-blue") color_default;;

let inputs = Conf.project_dir^"/ocamllibs/test/synthlib/";;

let on_input input =
  printf "%sInput: %s%s@." (color "green") input color_default;
  let parsed =
    try
      parsechan (open_in (project_dir^"/ocamllibs/test/synthlib/"^input))
    with Syparser.Error as e ->
      (print_err_std "Failed to parse input\n"; raise e)
  in
  printsy parsed;;

let children = Sys.readdir inputs in
let filter s = (not (String.contains s '~'))
               && (not (String.contains s '*'))
               && (not (String.contains s '#')) in
Array.iter  (fun s -> if filter s then on_input s) children;;
