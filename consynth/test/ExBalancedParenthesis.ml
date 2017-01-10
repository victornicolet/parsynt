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

let bal, count, i, a, n =
  make_bool_varinfo "bal",
  make_int_varinfo "cnt",
  make_int_varinfo "i",
  make_bool_array_varinfo "a",
  make_int_varinfo "m"


let _S_ = _s [bal; count]
let all_vs =  VS.union _S_ (_s [i; a; n])

let s, (ini, g, u) = VS.singleton i,
           (_let ([(var i, sk_zero)]),
            _b (evar i) Lt (evar n),
            _let [(var i, _b (evar i) Plus sk_one)])

let reach_const =
  IM.add count.vid sk_zero (IM.add bal.vid sk_true IM.empty)

let _f_ =
  _letin
    [(var count,
      _b (evar count) Plus (_Q (a $ (evar i)) sk_one (_u Neg sk_one)))]
    (_let [(var bal, _b (evar bal) And (_b (evar count) Ge sk_zero))]);;

VariableDiscovery.debug := true;;
VariableDiscovery.debug_dev := true;;

let name = "balanced_parenthesis"

let sketch_info =
  {
    id = 0;
    loop_name = name;
    ro_vars_ids = [a.vid];
    scontext = { state_vars = _S_; all_vars = VS.union _S_ all_vs; index_vars = s; costly_exprs = ES.empty};
    loop_body = _f_;
    join_body = SkLetExpr ([]);
    join_solution = Ast.Id_e "unsat";
    init_values = Some [];
    sketch_igu = s, (ini, g, u);
    reaching_consts = reach_const;
  };;

let context = { state_vars = _S_; index_vars = (VS.singleton i); all_vars = all_vs; costly_exprs = ES.empty }
let new_sketch  = discover sketch_info

let new_f_ =
  SketchTypes.complete_final_state new_sketch.scontext.state_vars
    (Sketch.Body.optims new_sketch.loop_body);;

IH.copy_into VariableDiscovery.discovered_aux
  SketchJoin.auxiliary_variables;;

let _join_ = Sketch.Join.build new_sketch.scontext.state_vars new_sketch.loop_body

let sketch_info = { new_sketch with join_body = _join_ };;



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
