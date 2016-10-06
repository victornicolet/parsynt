
exception Runtime of string

let runtime (s : string) : 'a = raise (Runtime s)

let listify (x : string list) : string =
  "(" ^ (String.concat " " x) ^ ")"

let listify_mult (x : string list) : string =
  match x with [s] -> s | _ -> listify x
