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

open Format
open Project_dir


(**
   1 - General settings.
   2 - Builtin variables.
   3 - Verification conditions settings.
   4 - Synthesis parameters (grammar macros names, ...)
   5 - Naming conventions.
   6 - Available solvers.
*)

let verbose = ref false

module SH =
  Hashtbl.Make (struct
    type t = String.t
    let equal s1 s2 = s1=s2
    let hash s = Hashtbl.hash s
  end)

let (>>) l n = List.nth l n

let project_dir = Project_dir.base
let source_dir = Project_dir.src
let output_dir = ref project_dir
let templates_dir = Project_dir.templates

let project_file rel_path =
  project_dir^"/"^rel_path

let source_file rel_path =
  source_dir^"/"^rel_path

let template template_name =
  templates_dir^"/"^template_name

let import file_name separator =
  let reg_separator = Str.regexp separator in
  let conf_file = SH.create 32 in
  try
    let ic = open_in file_name in
    (* Skip the first line, columns headers *)
    let _ = input_line ic in
    try
      while true; do
        (* Create a list of values from a line *)
        let line_list = Str.split reg_separator (input_line ic) in

        if !verbose then
          printf "Setting %s: %a@." (List.hd line_list)
            (pp_print_list (fun fmt a -> fprintf fmt "%s" a))
            (List.tl line_list);
        if List.length (List.tl line_list) > 0 then
          SH.add conf_file (List.hd line_list) (List.tl line_list)
        else
          SH.add conf_file (List.hd line_list) [""]
      done;
      conf_file
    with
    | End_of_file -> close_in ic; conf_file
  with
  | e -> raise e;;


let main_conf_file = import (source_file "conf/conf.csv") ","


let get_conf_string key =
  try
    List.hd (SH.find main_conf_file key)
  with
  | Not_found ->
    eprintf "There is not setting for %s. \
             There must be a missing setting in conf.csv !"
      key;
    raise Not_found

let get_conf_int key =
  try
    int_of_string (List.hd (SH.find main_conf_file key))
  with
  | Not_found ->
    eprintf "There is not setting for %s. \
             There must be a missing setting in conf.csv !@."
      key;
    raise Not_found
  | Failure s when s = "int_of_string" ->
    (eprintf "There is a setting for %s, but it is not an int.\
              Found %s."
       key
       (List.hd (SH.find main_conf_file key));
     raise (Failure s))
  | Failure s ->
    (eprintf "There is a setting for %s, but there was an error getting it.\
              Found %s."
       key
       (List.hd (SH.find main_conf_file key));
     raise (Failure s))

(** 2 - Builtin variable, such as min integer, max integer ... *)
type builtins =
  | Min_Int
  | Max_Int
  | False
  | True


let builtin_var_names = ["__MIN_INT_", Min_Int ;
                         "__MAX_INT_", Max_Int;
                         "__FALSE_", False;
                         "__TRUE_", True]


let is_builtin_var s = List.mem_assoc s builtin_var_names

let get_builtin s = List.assoc s builtin_var_names


(** 3 - Parameters of the verification condition of the synthesis *)
let verif_params_filename =
  source_file "conf/verification.params"

let verification_parameters =
  let reg_separator = Str.regexp "," in
  let list = ref [] in
  try
    let ic = open_in verif_params_filename in
    (* Skip the first line, columns headers *)
    let _ = input_line ic in
    try
      while true; do
        (* Create a list of values from a line *)
        let line_list = Str.split reg_separator (input_line ic) in
        if List.length line_list >= 3 then
          begin
            (if !verbose then
               printf "%a@."
                 (pp_print_list
                    ~pp_sep:(fun fmt () -> fprintf fmt ",")
                    (fun fmt a -> fprintf fmt "%s" a)) line_list);
            list := (int_of_string (line_list >> 0),
                     int_of_string (line_list >> 1),
                     int_of_string (line_list >> 2)):: !list
          end
        else ()
      done;
      !list
    with
    | End_of_file -> close_in ic; !list
  with
  | e ->
    eprintf "Please check verification parameters. Error while loading.@.";
    raise e;;


(* 5 - Naming conventions *)
let inner_loop_func_name func lid =
  "_L_"^(Str.first_chars func 4)^"@"^(string_of_int lid)

let is_inner_loop_func_name name =
  if String.length name > 3 then String.sub name 0 3  = "_L_" else false

let id_of_inner_loop name =
  try
    let elts =  Str.split (Str.regexp "@") name in
    int_of_string (List.nth elts ((List.length elts)-1))
  with e ->
    Format.eprintf "%s%s%s@."
      __FILE__ "id_of_inner_loop" "Failed to parse id of loop.";
    raise e


let join_name fname =   "join"^fname
let seq_name fname =   "^"^fname


(* 6 - Available solvers. *)
type solver = { name: string; extension: string; execname: string;}

let rosette = { name = "Rosette"; extension = ".rkt"; execname = "racket"}
let cvc4 = { name = "CVC4"; extension = ".sl"; execname = "CVC4"}
