open Format
type racket_struct = string * (string list)

(** Functions to print Racket constructs *)

let pp_struct_defintion fmt (sname, fields) =
  fprintf fmt "@[<1>(struct %s (%a))@;@]"
    sname
    (pp_print_list
       ~pp_sep:(fun f _ -> fprintf f " ")
       (fun f s -> fprintf f "%s" s)) fields

let pp_struct_equality fmt (sname, fields) =
  fprintf fmt "(define (%s-eq? s1 s2)@;(and %a))"
    sname
    (pp_print_list
       ~pp_sep:(fun f _ -> fprintf f " ")
       (fun f s ->
         fprintf f "@[<2>(eq? (%s-%s s1) (%s-%s s2))@]@;"
           sname s sname s)) fields


let pp_assignments state_struct_name state_name fmt =
  pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt "@;")
    (fun fmt (var_name, field_name) -> Format.fprintf fmt "[%s (%s-%s %s)]"
      var_name state_struct_name field_name state_name) fmt


let pp_comment fmt str =
  Format.fprintf fmt ";;%s@." str

let pp_body_app fmt (body_name, s, from, to_n) =
  Format.fprintf fmt "@[<hov 2>(%s %s %i %i)@]"
    body_name s from to_n
