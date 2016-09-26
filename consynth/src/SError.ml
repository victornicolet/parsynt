open Format
open SketchTypes
open SPretty

exception Exception_on of string * string

let raise_on except_name msg pp_obj obj =
  raise
    (Exception_on (except_name,
                   (fprintf str_formatter
                      "%s@.Failed on %s:%a@." msg except_name pp_obj obj;
                    flush_str_formatter ())))

let exception_on_variable msg var =
  raise_on "variable" msg pp_sklvar var

let exception_on_expression msg expr =
  raise_on "expression" msg pp_skexpr expr

let exception_on_function msg sklet  =
  raise_on "function" msg pp_sklet sklet


exception Skip_loop of string

let skip_exn msg =
  raise (Skip_loop msg)
