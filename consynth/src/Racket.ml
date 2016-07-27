open Format

type racket_struct = string * (string list)

let pp_struct_defintion fmt (sname, fields) =
  fprintf fmt "@[<1>(struct %s (%a))@;@]"
    sname
    (pp_print_list
       ~pp_sep:(fun f _ -> fprintf f " ")
       (fun f s -> fprintf f "%s" s)) fields

let pp_struct_equality fmt (sname, fields) =
  fprintf fmt "(define (%s-eq? s1 s2) (and %a))"
    sname
    (pp_print_list
       ~pp_sep:(fun f _ -> fprintf f " ")
       (fun f s ->
         fprintf f "@[<2>(eq? (%s-%s s1) (%s-%s s2))@]@;"
           sname s sname s)) fields
