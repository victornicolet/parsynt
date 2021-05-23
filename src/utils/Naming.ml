(* I/O file utils *)
open Base
open Stdio
open Config

let tmp_file_index = ref 0

let tmp_file (base : string) (extension : string) : string =
  let i = !tmp_file_index in
  let hd = Caml.Filename.remove_extension (Caml.Filename.basename !master_file) in
  tmp_file_index := i + 1;
  tmp_dir ^ "/" ^ hd ^ "_" ^ base ^ Int.to_string i ^ extension

let copy_file from_filename to_filename =
  let oc = Out_channel.create to_filename in
  let ic = In_channel.create from_filename in
  try
    while true do
      let line = In_channel.input_line_exn ic in
      Out_channel.output_string oc (line ^ "\n")
    done
  with End_of_file ->
    In_channel.close ic;
    Out_channel.close oc

let remove_in_dir dirname =
  try
    if Stdlib.Sys.is_directory dirname then
      let filenames = Stdlib.Sys.readdir dirname in
      let complete_fn = Array.map ~f:(fun s -> dirname ^ s) filenames in
      Array.iter
        ~f:(fun filename ->
          if Stdlib.Sys.is_directory filename then () else Stdlib.Sys.remove filename)
        complete_fn
    else raise (Sys_error "Not a directory name")
  with Sys_error s -> eprintf "Remove_in_dir : %s" s

(* Other naming conventions *)
module Rosette = struct
  let join_left_state_prefix = "$L"

  let join_right_state_prefix = "$L"

  let struct_name = "$"
end

let new_accumulator = "_acc"

let new_accumulator_struct = "$accum"

let new_struct_field = "m"

let new_struct_list_field = "l"

let struct_equality_name s = s ^ "-equal?"

let sep_str = "#"

let name_len = 4

let inner_loop_func_name func lid =
  sep_str ^ "L_" ^ Str.first_chars func name_len ^ sep_str ^ Int.to_string lid

let is_inner_loop_func_name name =
  if String.length name > 3 then String.(sub name ~pos:0 ~len:3 = sep_str ^ "L_") else false

let id_of_inner_loop name =
  try
    let elts = Str.split (Str.regexp sep_str) name in
    Int.of_string (List.nth_exn elts (List.length elts - 1))
  with e ->
    Fmt.(pf stderr "%s%s%s@." Caml.__FILE__ "id_of_inner_loop" "Failed to parse id of loop.");
    raise e

let join_name fname = "join" ^ fname

let seq_name fname = "seq:" ^ fname

let is_inner_join_name name =
  let elts = Str.split (Str.regexp sep_str) name in
  List.length elts >= 3
  && String.(sub (List.nth_exn elts 0) ~pos:0 ~len:4 = "join")
  && String.(sub (List.nth_exn elts 1) ~pos:0 ~len:2 = "L_")

let strip_contextual_prefix (s : string) =
  let prefixes = [ Rosette.join_left_state_prefix; Rosette.join_right_state_prefix ] in
  List.fold
    ~f:(fun s _prefix ->
      let sl = String.length s in
      let pl = max (String.length _prefix) (sl - 1) in
      if sl > 1 && String.(sub s ~pos:0 ~len:pl = _prefix) then
        String.(sub s ~pos:pl ~len:(Int.max (sl - pl) 0))
      else s)
    ~init:s prefixes

(* File extensions, *)
let ext_racket = ".rkt"
