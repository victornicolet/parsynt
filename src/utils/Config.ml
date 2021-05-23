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

open Base
open Stdio

(* ========================================================================= *)
(*                          GLOBAL FLAGS                                     *)
(* ========================================================================= *)
let verbose = ref false

let skip_predicate_discovery = ref false

let skip_first_solve = ref false

let break_problem = ref true

let always_use_lwt = ref true

let default_lift = ref 0

let minic_input = ref true

let parse_minic_only = ref false

let master_file = ref "undef"

(* Other verbosity flags *)
let complexity_verbose = ref 0

(* Symbolic execution parameters *)

let symbexe_unfolding_len = ref 3

let sfsp_synt_len = ref 4

let sl_join_synt_len = ref 5

let sfsp_sketch_complex = ref 0

(* Bounds on synthesis main loop *)

let cmax = ref 3

let budget_not_specified = ref true

let dump_solutions = ref false

let k = ref (-1)

let set_k (s : string) =
  try
    let n = Int.of_string s in
    if n < 0 || n > 2 then (
      Log.error_msg "k should be be between 0 and 2 inclusive.";
      failwith "Please specify a valid value for k.")
    else k := n
  with _ -> Log.warning_msg "Failed to parse value of k. Ignoring provided value."

let m = ref (-1)

let set_m (s : string) =
  try
    let n = Int.of_string s in
    if n < 2 then (
      Log.error_msg "m should be >= 2..";
      failwith "Please specify a valid value for m.")
    else m := n
  with _ -> Log.warning_msg "Failed to parse value of m. Ignoring provided value."

let c = ref (-1)

let set_c (s : string) =
  try
    let n = Int.of_string s in
    if n < 2 then (
      Log.error_msg "c should be >= 2..";
      failwith "Please specify a valid value for c.")
    else c := n
  with _ -> Log.warning_msg "Failed to parse value of c. Ignoring provided value."

(* Performance parameters *)
let num_parallel_processes = 4

let timeout_sfsp_synt = 100

(* Programs : TODO *)
let racket = FileUtil.which "racket"

let z3 = FileUtil.which "z3"

let tmp_dir = Caml.Filename.get_temp_dir_name ()

let project_dir = Project_dir.base

let source_dir = Project_dir.src

let output_dir = ref project_dir

let templates_dir = Project_dir.templates

let project_file rel_path = project_dir ^ "/" ^ rel_path

let source_file rel_path = source_dir ^ "/" ^ rel_path

let template template_name = templates_dir ^ "/" ^ template_name

let import file_name separator =
  let reg_separator = Str.regexp separator in
  let conf_file = Hashtbl.create (module String) ~size:32 in
  try
    let ic = Stdio.In_channel.create file_name in
    (* Skip the first line, columns headers *)
    let _ = Stdio.In_channel.input_line ic in
    try
      while true do
        (* Create a list of values from a line *)
        match Stdio.In_channel.input_line ic with
        | Some l -> (
            let line_list = Str.split reg_separator l in
            match line_list with
            | [ hd ] -> Hashtbl.set conf_file ~key:hd ~data:[ "" ]
            | hd :: tl -> Hashtbl.set conf_file ~key:hd ~data:tl
            | _ -> ())
        | None -> raise End_of_file
      done;
      conf_file
    with End_of_file ->
      In_channel.close ic;
      conf_file
  with e -> raise e

let main_conf_file = import (source_file "conf/conf.csv") ","

let get_conf_string key =
  match Hashtbl.find main_conf_file key with
  | Some data -> List.hd data
  | None ->
      eprintf "There is not setting for %s. There must be a missing setting in conf.csv !" key;
      None

let get_conf_int key =
  try Int.of_string (List.hd_exn (Hashtbl.find_exn main_conf_file key)) with
  | Caml.Not_found ->
      eprintf "There is not setting for %s. There must be a missing setting in conf.csv !@." key;
      raise Caml.Not_found
  | Failure s when String.(s = "int_of_string") ->
      eprintf "There is a setting for %s, but it is not an int.Found %s." key
        (List.hd_exn (Hashtbl.find_exn main_conf_file key));
      raise (Failure s)
  | Failure s ->
      eprintf "There is a setting for %s, but there was an error getting it.Found %s." key
        (List.hd_exn (Hashtbl.find_exn main_conf_file key));
      raise (Failure s)

(** 2 - Builtin variable, such as min integer, max integer ... *)
type builtins = Min_Int | Max_Int | False | True

let builtin_var_names =
  [ ("__MIN_INT_", Min_Int); ("__MAX_INT_", Max_Int); ("__FALSE_", False); ("__TRUE_", True) ]

let is_builtin_var s = List.Assoc.mem s builtin_var_names

let get_builtin s = List.Assoc.find_exn s builtin_var_names

(** 3 - Parameters of the verification condition of the synthesis *)
let verif_params_filename = source_file "conf/verification.params"

let verification_parameters =
  let reg_separator = Str.regexp "," in
  let list = ref [] in
  try
    let ic = In_channel.create verif_params_filename in
    (* Skip the first line, columns headers *)
    let _ = In_channel.input_line ic in
    try
      while true do
        match In_channel.input_line ic with
        | Some l ->
            (* Create a list of values from a line *)
            let line_list = Str.split reg_separator l in
            if List.length line_list >= 3 then
              list :=
                ( Int.of_string (List.nth_exn line_list 0),
                  Int.of_string (List.nth_exn line_list 1),
                  Int.of_string (List.nth_exn line_list 2) )
                :: !list
            else ()
        | None -> raise End_of_file
      done;
      !list
    with End_of_file ->
      In_channel.close ic;
      !list
  with e ->
    eprintf "Please check verification parameters. Error while loading.@.";
    raise e

(* 5 - Naming conventions *)

(* 6 - Available solvers. *)
type solver = { name : string; extension : string; execname : string }

let rosette = { name = "Rosette"; extension = ".rkt"; execname = "racket" }

let cvc4 = { name = "CVC4"; extension = ".sl"; execname = "CVC4" }
