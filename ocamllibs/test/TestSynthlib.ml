open Conf
open Format
open Synthlib
open Utils.PpTools;;

let on_input input =
  printf "%sInput: %s%s@." (color "green") input color_default;
  try
    let _ =
      parsechan (open_in (project_dir^"/ocamllibs/test/synthlib/"^input))
    in
    printf "%s%sOK%s@." (color "black") (color "b-green") color_default
  with Syparser.Error->
    print_err_std "Failed to parse input.\n"




let test () =
  printf "%s********* TESTING SYNTHLIB2 PARSER **********%s@."
    (color "b-blue")
    color_default;
  let children = Sys.readdir (Conf.project_dir^"/ocamllibs/test/synthlib/") in
  let filter s = (not (String.contains s '~'))
                 && (not (String.contains s '*'))
                 && (not (String.contains s '#')) in
  Array.iter  (fun s -> if filter s then on_input s) children
