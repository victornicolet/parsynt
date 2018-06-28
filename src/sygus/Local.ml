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


let exec_solver (timeout : int) (solver : solver) (filename : string) : int * float =
  let start = Unix.gettimeofday () in
  (* Execute on filename. *)
  let errcode =
    match solver.name with
    | "Rosette" -> Sys.command (Racket.silent_racket_command_string timeout filename)
    | "CVC4" -> Sys.command (Racket.silent_racket_command_string timeout filename)
    | _ -> Sys.command (Racket.silent_racket_command_string timeout filename)
  in
  let elapsed = (Unix.gettimeofday ()) -. start in
  if !debug then
    Format.printf "@.%s : executed in %.3f s@." solver.name elapsed;
  errcode, elapsed


let compile
    ?(solver=Conf.rosette)
    ?(print_err_msg = default_error)
    (timeout : int)
    (printer : Format.formatter -> 'a -> 'b)
    (printer_arg : 'a) : bool * float * string =

  let solution_tmp_file = Filename.temp_file "parsynt_solution_" solver.extension in
  let sketch_tmp_file = Filename.temp_file "parsynt_sketch_" solver.extension in
  completeFile sketch_tmp_file solution_tmp_file printer printer_arg;
  (* Consider a break in the solver execution as a timeout. Thsi enables the user to
     terminate a call that is lasting too long and thus allows to 'continue' with
     the different steps of the algorithm.
  *)
  Sys.catch_break true;
  let errno, elapsed =
    try
      exec_solver timeout solver sketch_tmp_file
    with Sys.Break ->
      124, -1.0
  in
  if !dump_sketch || (errno != 0 && !debug) then
    begin
      remove_in_dir dumpDir;
      let dump_file = dumpDir^(Filename.basename sketch_tmp_file)  in
      copy_file sketch_tmp_file dump_file;
      eprintf "%sDumping sketch file in %s%s%s\n"
        (PpTools.color "b-red") (PpTools.color "hi-underlined") dump_file
        (PpTools.color_default);
    end;
  (* Continue: signal that algorithm should continue without solution. *)
  let continue =
    if errno != 0 then
      begin
        if errno = 124 || errno = 255 then
          begin
            Format.printf "@.[INFO] Solver terminated / stopped by user.@.";
            true
          end
        else
          begin
            Format.printf "[ERROR] Errno : %i@." errno;
            if !debug then
              begin
                print_err_msg errno;
              end;
            (* ignore(Sys.command ("cat "^sketch_tmp_file)); *)
            Sys.remove sketch_tmp_file;
            exit 1;
          end;
      end
    else
      false
  in
  Sys.remove sketch_tmp_file;
  continue, elapsed, solution_tmp_file


let fetch_solution ?(solver=rosette) filename =
  match solver.name with
  | "Rosette" ->
    let parsed =
      try
        Racket.parse_scm (Std.input_file filename)
      with e ->
        (let err_code = Sys.command ("cat "^filename) in
         Format.printf "@.cat %s : %i@." filename err_code;
         match e with
         | Rparser.Error -> raise e
         | Rlexer.LexError s ->
           eprintf "%s" s; raise e
         | e ->
           eprintf "Failure while parsing %s with simplify_parse_scm.@."
             filename;
           raise e)
    in
    Sys.remove filename;
    parsed
  (* TODO *)
  | "CVC4" -> [RAst.Int_e(-1)]
  | _ -> [RAst.Int_e(-1)]



let compile_and_fetch
    ?(timeout=(-1))
    ?(print_err_msg = default_error)
    (solver: solver)
    (printer : Format.formatter -> 'a -> 'b)
    (printer_arg : 'a) =
  let continue, elapsed, filename =
    compile ~solver:solver ~print_err_msg:print_err_msg timeout printer printer_arg
  in
  if continue then -1.0, [] else elapsed, fetch_solution filename
