open Str
open Printf
open Parser
open Racket
(**
    Locally, solving sketches is done by writing to files,
    executing a compiled racket program and then retrieving the result
    in a file.
*)

let debug = ref false
let dump_sketch = ref false

let templateDir = Filename.current_dir_name^"/templates/"
let dumpDir = Filename.current_dir_name^"/dump/"

let copy_file from_filename to_filename =
  let oc = open_out to_filename in
  let ic = open_in from_filename in
  try
    while true do
      let line = input_line ic in
      output_string oc (line^"\n");
    done
  with End_of_file ->
    begin
      close_in ic;
      close_out oc
    end


let remove_in_dir dirname =
  try
    begin
      if Sys.is_directory dirname then
        begin
          let filenames = Sys.readdir dirname in
          let complete_fn =
            Array.map (fun s -> dirname^s) filenames in
          Array.iter
            (fun filename ->
              if Sys.is_directory filename then
                ()
              else
                Sys.remove filename)
            complete_fn
        end
      else
        raise (Sys_error "Not a directory name")
    end
  with
    Sys_error s ->
      eprintf "Remove_in_dir : %s" s

let line_stream_of_channel channel =
  Stream.from
    (fun _ ->
      try Some (input_line channel) with End_of_file -> None);;

let completeFile filename solution_file_name sketch_printer sketch =
  let oc = open_out filename in
  let process_line line =
    fprintf oc "%s\n"
      (Str.global_replace (regexp_string "%output-file%")
         solution_file_name line)
  in
  let header = open_in (templateDir^"header.rkt") in
  Stream.iter process_line (line_stream_of_channel header);
  let fmt = Format.make_formatter
    (output oc)  (fun () -> flush oc) in
  sketch_printer fmt sketch;
  let footer = open_in (templateDir^"footer.rkt") in
  Stream.iter process_line (line_stream_of_channel footer);
  close_out oc

let default_error i =
  eprintf "Errno %i : Error while running racket on sketch.\n" i

let racket filename =
  let start = Unix.gettimeofday () in
  let errcode = Sys.command ("racket "^filename) in
  let elapsed = (Unix.gettimeofday ()) -. start in
  Format.printf "@.Racket : executed in %.3f s@." elapsed;
  errcode

let compile ?(print_err_msg = default_error) printer printer_arg =
  let solution_tmp_file = Filename.temp_file "conSynthSol" ".rkt" in
  let sketch_tmp_file = Filename.temp_file "conSynthSketch" ".rkt" in
  completeFile sketch_tmp_file solution_tmp_file printer printer_arg;
  let errno = racket sketch_tmp_file in
  if !dump_sketch || (errno != 0 && !debug) then
    begin
      remove_in_dir dumpDir;
      let dump_file = dumpDir^(Filename.basename sketch_tmp_file)  in
      copy_file sketch_tmp_file dump_file;
      eprintf "Dumping sketch file in %s\n" dump_file;
      ignore(Sys.command ("cat "^dump_file));
    end;
  Sys.remove sketch_tmp_file;
  if errno != 0 then
    begin
      if !debug then
        begin
          print_err_msg errno;
        end;
      exit 1;
    end;
  errno, solution_tmp_file

let fetch_solution filename =
  let parsed =
    try
      List.map
        clean
        (Parser.main Lexer.token (Lexing.from_string (Std.input_file filename)))
    with e ->
      (let err_code = Sys.command ("cat "^filename) in
       Format.printf "@.cat %s : %i@." filename err_code;
       match e with
       | Parser.Error -> raise e
       | Lexer.LexError s ->
         eprintf "%s" s; raise e
       | _ -> raise e)

  in
  Sys.remove filename;
  parsed


let compile_and_fetch ?(print_err_msg = default_error) printer printer_arg =
  let errno, filename =
    compile ~print_err_msg:print_err_msg printer printer_arg
  in
  fetch_solution filename
