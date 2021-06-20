open Fmt

exception Runtime of string

let runtime (s : string) : 'a = raise (Runtime s)

let listify (x : string list) : string = "(" ^ String.concat " " x ^ ")"

let pp_list_scm fmt (l, f) =
  pf fmt "(%a)" (fun fmt l -> list ~sep:(fun fmt () -> string fmt " ") f fmt l) l

let listify_mult (x : string list) : string = match x with [ s ] -> s | _ -> listify x
