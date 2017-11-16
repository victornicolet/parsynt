open Consynth
open Format

type test_unit =
  {
    name : string;
    body : string;
  }

let pp_test_unit t =
  printf "Test for %s...@." t.name;
  try
    let res = Racket.simplify_parse_scm t.body in
    printf "Success : %a@." RAst.pp_expr_list res
  with e ->
    printf "Failure.@.";
    raise e

let tests =
  [{ name = "function_def";
     body = "(define (f x) (+ x 20))";};
   { name = "function_def_with_let";
     body = "(define (f x) (let ((i 20)) (+ i 20)))";};
   { name = "function_def_with_let2";
     body = "(define (f2 x) (let ((i 20)) (+ (f x) i)))";};
   { name = "function_with_hole";
     body = "(define (holef x y) (+ x y))";};
   { name = "function_with_hole_op";
     body = "(define (t cnt)\
             (cnt (+ l.cnt (if ((BinopsBool 0) x.bal x.bal) x.cnt x.cnt))))";};
   { name = "test_is_sorted";
     body = "(define (__join__ $L $R)
             (let ((l.bal ($-bal $L)) (l.cnt ($-cnt $L))
             (l.aux_3 ($-aux_3 $L)) (x.bal ($-bal $R)) (x.cnt ($-cnt $R))
             (x.aux_3 ($-aux_3 $R)))
             (let ((bal (&& l.bal (>= (+ (- l.cnt -3)
             (if ((BinopsBool 0) x.bal x.bal) 1 (- x.cnt x.cnt)))
             (- 3 x.aux_3))))
             (cnt (+ l.cnt (if ((BinopsBool 0) x.bal x.bal) x.cnt x.cnt))))
             ($ bal cnt (min (+ x.aux_3 l.cnt) l.aux_3)))))";}
  ]

let main () =
  List.iter pp_test_unit tests


  (* let test_process_file name = *)
  (*   let ic = open_in name in *)
  (*   let parsed_exprs = Racket.parse_scm ic in *)
