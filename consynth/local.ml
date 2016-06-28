open Str
open Printf
(**
    Locally, solving sketches is done by writing to files,
    executing a compiled racket program and then retrieving the result
    in a file.
*)

let templateDir = Filename.current_dir_name^"/templates/"

let line_stream_of_channel channel =
    Stream.from
      (fun _ ->
         try Some (input_line channel) with End_of_file -> None);;

let completeFile filename solname sketch =
  let oc = open_out filename in
  let process_line line =
    fprintf oc "%s\n"
      (Str.global_replace (regexp_string "%output-file%") solname line)
  in
  let header = open_in (templateDir^"header.rkt") in
  Stream.iter process_line (line_stream_of_channel header);
  Stream.iter process_line  sketch;
  let footer = open_in (templateDir^"footer.rkt") in
  Stream.iter process_line (line_stream_of_channel footer);
  close_out oc


let racket filename =
  Sys.command ("racket "^filename)

let compile sketch =
  let solution_tmp_file = Filename.temp_file "conSynthSol" ".rkt" in
  let sketch_tmp_file = Filename.temp_file "conSynthSketch" ".rkt" in
  completeFile sketch_tmp_file solution_tmp_file sketch;
  let errno = racket sketch_tmp_file in
  Sys.remove sketch_tmp_file;
  errno, solution_tmp_file

let fetch_solution filename =
  (**
      TODO : parse the solution given by racket into a set of Cil
     expressions.
  *)
  let is = line_stream_of_channel (open_in filename) in
  let process_line line =
    print_endline line
  in
  Stream.iter process_line is;
  Sys.remove filename


let test () =
  let isketch = line_stream_of_channel (open_in (templateDir^"sketch.rkt")) in
  let err, solFileName = compile isketch in
  fetch_solution solFileName;;

test ()
