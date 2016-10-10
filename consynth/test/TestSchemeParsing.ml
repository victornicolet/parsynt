open Consynth


let function_def = "(define (f x) (+ x 20))"
let function_def_with_let = "(define (f x) (let ((i 20)) (+ i 20)))"
let function_def_with_let2 = "(define (f x) (let ((i 20)) (+ i 20)))"

let main () =
  let fdef = Racket.parse_scm function_def in
  Ast.pp_expr_list Format.std_formatter fdef;
  let fdefwl = Racket.parse_scm function_def_with_let in
  Ast.pp_expr_list Format.std_formatter fdefwl;
