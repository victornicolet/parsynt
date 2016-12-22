open Consynth


let function_def = "(define (f x) (+ x 20))"
let function_def_with_let = "(define (f x) (let ((i 20)) (+ i 20)))"
let function_def_with_let2 = "(define (f2 x) (let ((i 20)) (+ (f x) i)))"

let main () =
  let fdef = Racket.parse_scm function_def in
  Ast.pp_expr_list Format.std_formatter fdef;
  let fdefwl = Racket.parse_scm (function_def_with_let^function_def_with_let2) in
  Ast.pp_expr_list Format.std_formatter fdefwl;

  (* let test_process_file name = *)
  (*   let ic = open_in name in *)
  (*   let parsed_exprs = Racket.parse_scm ic in *)
