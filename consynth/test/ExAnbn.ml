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

let an, bn, i, ar, a, b, n =
  make_bool_varinfo "an",
  make_bool_varinfo "bn",
  make_int_varinfo "i",
  make_int_array_varinfo "ar",
  make_int_varinfo "a",
  make_int_varinfo "b",
  make_int_varinfo "m"


let _S_ = _s [an; bn]
let all_vs =  VS.union _S_ (_s [i; ar; a; b; n])

let sigu = VS.singleton i,
           (_let ([(var i, sk_zero)]),
            _b (evar i) Lt (evar n),
            _let [(var i, _b (evar i) Plus sk_one)])

let reach_const =
  IM.add an.vid sk_true (IM.add bn.vid sk_true IM.empty)

let _f_ =
  _letin
    [(var an,
     _b (_b (ar $ (evar i)) Eq (evar a)) And (evar an))]
    (_let [(var bn, _b (_b (_b ((ar $ (evar i))) Eq (evar b))
                          Or
                          (evar an))
              And (evar bn))]);;

VariableDiscovery.debug := true;;
VariableDiscovery.debug_dev := true;;

let new_S_, new_f_  = discover _S_ _f_ sigu

let new_f_ =
  SketchTypes.complete_final_state new_S_ (Sketch.Body.optims new_f_);;

IH.copy_into VariableDiscovery.discovered_aux
  SketchJoin.auxiliary_variables;;

let _join_ = Sketch.Join.build new_S_ new_f_

let name = "anbn"

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
