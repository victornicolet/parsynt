open Format

exception Runtime of string

let runtime (s : string) : 'a = raise (Runtime s)

let listify (x : string list) : string =
  "(" ^ (String.concat " " x) ^ ")"

let pp_list_scm fmt (l,f) =
  fprintf fmt "(%a)"
    (fun fmt l ->
       pp_print_list
         ~pp_sep:(fun fmt () -> pp_print_string fmt " ")
         f fmt l)
    l

let listify_mult (x : string list) : string =
  match x with [s] -> s | _ -> listify x
