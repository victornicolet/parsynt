open Cil
open Format
open Local
open PpHelper
open Utils
open TestUtils
open SketchTypes
open Canalyst

(* C implementation with auxiliary variables

   int max_length_of_1 (_Bool *a, int n) {
   int cl = 0;
   int ml = 0;
   int c = 0;
   _Bool conj = 1;

   for (int i = 0; i < n; i++) {
    conj = conj && a[i];
    c = c + (conj ? 1 : 0);
    cl = a[i] ? cl + 1 : 0;
    ml = max (ml, cl);
   }
   return ml ;
   }
*)

let cl, ml, c, conj, a, n, i =
  make_int_varinfo "cl",
  make_int_varinfo "ml",
  make_int_varinfo "c",
  make_bool_varinfo "conj",
  make_bool_array_varinfo "a",
  make_int_varinfo "n",
  make_int_varinfo "i"

let stv = _s [cl; ml; c; conj]
let all_vs = VS.union stv (_s [a; n; i])

let reach_const =
  IM.add cl.vid sk_zero
    (IM.add ml.vid sk_zero
       (IM.add c.vid sk_zero
          (IM.add conj.vid sk_true IM.empty)))

let name = "max_length_of_1s"

let func =
  _letin
    [(var conj, _b (evar conj) And (a $ (evar i)));
     (var cl,   _Q (a $ (evar i)) (_b (evar cl) Plus sk_one) sk_zero)]
    (_let
       [(var ml, _b (evar ml) Max (evar cl));
        (var c, _b (evar c) Plus (_Q (evar conj) sk_one sk_zero))])

let sigu = VS.singleton i,
           (_let ([(var i, sk_zero)]),
            _b (evar i) Lt (evar n),
            _let [(var i, _b (evar i) Plus sk_one)])

let sketch_info =
  {
    loop_name = name;
    ro_vars_ids = [a.vid];
    state_vars = stv;
    var_set = all_vs;
    loop_body = complete_final_state stv func;
    join_body = complete_final_state stv (Sketch.Join.build stv func);
    sketch_igu = sigu;
    reaching_consts = reach_const;
  };;

Local.dump_sketch := true;;

try
  printf "@.SOLVING sketch for %s.@." name;
  let parsed =
    compile_and_fetch pp_sketch sketch_info
  in
  if List.exists (fun e -> (Ast.Str_e "unsat") = e) parsed then
    (* We get an "unsat" answer : add loop to auxliary discovery *)
    printf
      "@.%sNO SOLUTION%s found for %s with user-defined variables.@."
      (color "orange") default name
  else
    (* A solution has been found *)
    printf "@.%sSOLUTION for %s %s:@.%a"
      (color "green") name default Ast.pp_expr_list parsed;

with Failure s ->
  printf "@.%sFAILED to find a solution for %s%s.@."
    (color "red") name default;;
