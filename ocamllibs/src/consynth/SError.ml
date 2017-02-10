open Format
open SketchTypes
open SPretty


let debug_global = ref true
let set_debug_global () = debug_global := true
let unset_debug_global () = debug_global := false

exception Exception_on of string * string

let raise_on except_name msg pp_obj obj =
  let str_message =
    fprintf str_formatter
      "%s@.Failed on %s:%a@." msg except_name pp_obj obj;
    flush_str_formatter ()
  in
  raise
    (Exception_on (except_name, str_message))


let exception_on_variable msg var =
  raise_on "variable" msg pp_sklvar var

let exception_on_expression msg expr =
  raise_on "expression" msg pp_skexpr expr

let exception_on_function msg sklet  =
  raise_on "function" msg pp_sklet sklet


exception Skip_loop of string

let skip_exn msg =
  raise (Skip_loop msg)

exception Functional_conversion of string

let fail_functional_conversion str =
  raise (Functional_conversion str)

exception Sketch_generation of string

let fail_sketch_generation str =
  raise (Sketch_generation str)

(** Logging for debugging purposes *)
let logfile = ref "log"

let elog msg =
  let oc = open_out !logfile in
  let foc = formatter_of_out_channel oc in
  fprintf foc msg;
  close_out oc
