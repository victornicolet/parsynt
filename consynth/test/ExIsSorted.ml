open Cil
open Format
open Local
open PpHelper
open Utils
open TestUtils
open SketchTypes
open Canalyst
open VariableDiscovery

(* C implementation with auxiliary variables

   _Bool is_sorted (int *a, int n) {
     _Bool is_sorted = true;
     int prev = _min_int_;

     for (int i = 0; i < n; i++) {
       is_sorted = is_sorted && (a[i] > prev);
       prev = a[i];
   }
   return is_sorted;
   }
*)

let is_sorted, prev,  a, n, i =
  make_bool_varinfo "is_sorted",
  make_int_varinfo "prev",
  make_int_array_varinfo "a",
  make_int_varinfo "n",
  make_int_varinfo "i"

let old_stv = _s [is_sorted; prev]
let old_all_vs = VS.union old_stv (_s [a; n; i])

let reach_const =
  IM.add is_sorted.vid sk_true
    (IM.add prev.vid (SkConst NInfnty) IM.empty)

let name = "is_sorted";;

let old_func =
  _let [(var is_sorted, _b (evar is_sorted) And
           (_b (a $ (evar i)) Gt (evar prev)));
        (var prev, a $ (evar i))]



let sigu = VS.singleton i,
           (_let ([(var i, sk_zero)]),
            _b (evar i) Lt (evar n),
            _let [(var i, _b (evar i) Plus sk_one)]);;

(** Find new variables *)
VariableDiscovery.debug := true;;

let stv, func = discover old_stv old_func sigu

let all_vs = VS.union stv (_s [a; n; i])

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
