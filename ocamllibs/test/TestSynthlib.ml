open Conf
open Format
open Synthlib
open Synthlib2ast
open Utils.ListTools
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
  test_gen_arity_defs ()
