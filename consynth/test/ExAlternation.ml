open Format
open SketchTypes
open Cil
open Utils
open TestUtils
open VariableDiscovery
open Canalyst
open Local
open PpHelper
open SError

let prev, altern, i, a, n =
  make_bool_varinfo "prev",
  make_bool_varinfo "altern",
  make_int_varinfo "i",
  make_bool_array_varinfo "a",
  make_int_varinfo "m"


let _S_ = _s [prev; altern]
let all_vs =  VS.union _S_ (_s [i; a; n])

let sigu = VS.singleton i,
           (_let ([(var i, sk_zero)]),
            _b (evar i) Lt (evar n),
            _let [(var i, _b (evar i) Plus sk_one)])

let reach_const =
  IM.add prev.vid sk_true (IM.add altern.vid sk_true IM.empty)

let _f_ =
  _let
    [(var altern,
      _b (evar altern) And
        (_Q  (evar prev) (a $ (evar i)) (_u Not (a $ (evar i)))));
    (var prev, a $ (evar i))];;

VariableDiscovery.debug := true;;
VariableDiscovery.debug_dev := true;;

let new_S_, new_f_  = discover _S_ _f_ sigu

let new_f_ =
  SketchTypes.complete_final_state new_S_ (Sketch.Body.optims new_f_);;

IH.copy_into VariableDiscovery.discovered_aux
  SketchJoin.auxiliary_variables;;

let _join_ = Sketch.Join.build new_S_ new_f_

let name = "alternation_of_0_and_1"

let sketch_info =
  {
    loop_name = name;
    ro_vars_ids = [a.vid];
    state_vars = new_S_;
    var_set = VS.union new_S_ all_vs;
    loop_body = new_f_;
    join_body = _join_;
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
