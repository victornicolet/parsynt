(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
  *)

open Str
open Printf
open Rparser
open Synthlib2ast
open Synthlib
open Syparser
open Utils
open Conf
(**
    Locally, solving sketches is done by writing to files,
    executing a compiled racket program and then retrieving the result
    in a file.
*)

let debug = ref false
let dump_sketch = ref false

let dumpDir = Filename.concat Conf.project_dir "dump/"

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
  let header = open_in (Conf.template "header.rkt") in
  Stream.iter process_line (line_stream_of_channel header);
  let fmt = Format.make_formatter
    (output oc)  (fun () -> flush oc) in
  sketch_printer fmt sketch;
  let footer = open_in (Conf.template "footer.rkt") in
  Stream.iter process_line (line_stream_of_channel footer);
  close_out oc

let default_error i =
  eprintf "Errno %i : Error while running racket on sketch.\n" i

let exec_solver solver filename =
  let start = Unix.gettimeofday () in
  (* Execute on filename. *)
  let errcode =
    match solver.name with
    | "Rosette" -> Sys.command (Racket.silent_racket_command_string filename)
    | "CVC4" -> Sys.command (Racket.silent_racket_command_string filename)
    | _ -> Sys.command (Racket.silent_racket_command_string filename)
  in
  let elapsed = (Unix.gettimeofday ()) -. start in
  Format.printf "@.%s : executed in %.3f s@." solver.name elapsed;
  errcode, elapsed

let compile ?(solver=Conf.rosette) ?(print_err_msg = default_error)
    printer printer_arg =
  let solution_tmp_file = Filename.temp_file "parsynt_solution_" solver.extension in
  let sketch_tmp_file = Filename.temp_file "parsynt_sketch_" solver.extension in
  completeFile sketch_tmp_file solution_tmp_file printer printer_arg;
  let errno, elapsed = exec_solver solver sketch_tmp_file in
  if !dump_sketch || (errno != 0 && !debug) then
    begin
      remove_in_dir dumpDir;
      let dump_file = dumpDir^(Filename.basename sketch_tmp_file)  in
      copy_file sketch_tmp_file dump_file;
      eprintf "%sDumping sketch file in %s%s%s\n"
        (PpTools.color "b-red") (PpTools.color "hi-underlined") dump_file
        (PpTools.color_default);
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
  errno, elapsed, solution_tmp_file

let fetch_solution ?(solver=rosette) filename =
  match solver.name with
  | "Rosette" ->
    let parsed =
      try
        Racket.simplify_parse_scm (Std.input_file filename)
      with e ->
        (let err_code = Sys.command ("cat "^filename) in
         Format.printf "@.cat %s : %i@." filename err_code;
         match e with
         | Rparser.Error -> raise e
         | Rlexer.LexError s ->
           eprintf "%s" s; raise e
         | _ -> raise e)
    in
    Sys.remove filename;
    parsed
  (* TODO *)
  | "CVC4" -> [RAst.Int_e(-1)]
  | _ -> [RAst.Int_e(-1)]



let compile_and_fetch ?(print_err_msg = default_error)
    solver printer printer_arg =
  let errno, elapsed, filename =
    compile ~solver:solver ~print_err_msg:print_err_msg printer printer_arg
  in
  elapsed, fetch_solution filename
