open Format

let verbose = ref false

module SH =
  Hashtbl.Make (struct
    type t = String.t
    let equal s1 s2 = s1=s2
    let hash s = Hashtbl.hash s
  end)

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


let main_conf_file = import "conf.csv" ","


let get_conf_string key =
  try
    List.hd (SH.find main_conf_file key)
  with
  | Not_found ->
    eprintf "There is not setting for %s. \
             There must be a missing setting in conf.csv !"
      key;
    raise Not_found


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
