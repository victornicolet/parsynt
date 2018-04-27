open Cil
open Format
open FPretty
open Utils
open Utils.PpTools
open VariableDiscovery
open TestUtils
open FuncTypes


let test_1 () =
  (* Test variable discovery for mts *)
  let mts_vi = make_int_varinfo "mts" in
  let array_vi = make_int_array_varinfo "A" in
  let i = make_int_varinfo "i" in
  let n = make_int_varinfo "n" in
  let mts_func =
    _let
      [(var mts_vi),(_b (evar mts_vi) Max (array_vi $ (evar i)))]
  in
  let mts_figu : sigu =
    VarSet.singleton i,
    ((_let [(var i),sk_zero]),
    (_b (evar i) Lt (evar n)),
    (_let [(var i),(_b (evar i) Plus sk_one)]))
  in
  let rconsts =
    List.fold_left
      (fun map (e,v) -> IM.add e.vid v map) IM.empty [(mts_vi, sk_zero)]
  in
  let pb = discover
    {
      id = 0;
      loop_name = "mts_test";
      min_input_size = 0;
      host_function = {fvar = mkFnVar "__" Bottom; fformals = []; flocals = [] };
      inner_functions = [];
      scontext = {
        state_vars = VarSet.singleton mts_vi;
        index_vars = VarSet.singleton i;
        used_vars = VarSet.of_list [mts_vi; i; array_vi];
        all_vars = VarSet.of_list [mts_vi; i; array_vi];
        costly_exprs = ES.empty;
      };
      uses_global_bound = false;
      init_values = IM.empty;
      func_igu = mts_figu;
      loop_body = mts_func;
      join_sketch = sk_tail_state;
      memless_sketch = sk_tail_state;
      join_solution = sk_tail_state;
      memless_solution = sk_tail_state;
      reaching_consts = rconsts;
    }
  in
  VarSet.pp_var_names std_formatter pb.scontext.state_vars


let test () =
  printf "\t%s%s TEST VARIABLE DISCOVERY %s@."
    (color "b-green") (color "black") color_default;

  let var_bank = new namedVariables in
  var_bank#add_vars_by_name
    [
      ("v", "int");("w", "int");("x", "int");("y", "int");("z", "int");
      ("mps", "int");("mts", "int");("sum", "int");
      ("a", "bool");("b", "bool");("c","bool");
      ("X", "int array");("Y", "int array");
      ("A", "bool array");("B", "bool array")
    ];
    printf "\t%s%s OK: TEST PASSED %s@."
      (color "b-green") (color "black") color_default;
  test_1 ();
