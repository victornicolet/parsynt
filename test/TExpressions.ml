open Format
open SymbExe
open Utils
open Cil
open TestUtils
open PpTools
open FPretty
open ExpressionReduction
open Expressions
open VariableDiscovery

open FuncTypes

let x, y, z, a, b, c, a_n =
  FnVariable (make_int_varinfo "x"),
  FnVariable (make_int_varinfo "y"),
  FnVariable (make_int_varinfo "z"),
  FnVariable (make_int_varinfo "a"),
  FnVariable (make_bool_varinfo "b"),
  FnVariable (make_bool_varinfo "c"),
  FnVariable (make_int_array_varinfo "a_n")

let test_flatten_expression () =
  let e_1 =
    FnBinop (Plus, FnBinop (Plus, FnVar x , FnVar y),
             FnBinop (Plus, FnVar a,FnVar  b))
  in
  let e_2 = FnBinop (Times, e_1, FnBinop (Times, FnVar x, FnUnop (Neg, FnVar y))) in
  let e1_flat_ok, e2_flat_ok =
    (match flatten_AC e_1 with
     | FnApp (_, Some f, args4) ->
       f = get_AC_op Plus && List.length args4 = 4
     | _ -> false),
    (match flatten_AC e_2 with
     | FnApp (_, Some f, args3) ->
       f = get_AC_op Times && List.length args3 = 3 &&
       (* One of the elements of the list has to be (plus x y a b) *)
       (List.fold_left
          (fun found elt ->
             (match elt with
              | FnApp (_, Some fplus, args4) ->
                fplus = get_AC_op Plus && List.length args4 = 4
              | _ -> found))
          false args3)
     |_ -> false)
  in
  if e1_flat_ok && e2_flat_ok then
    msg_passed "Flatten expressions test passed."
  else
    msg_failed "Flatten expressions test failed."



let test_split_expression () =
  let tname = "Splitting expression according to costly expressions." in
  let vars = vardefs "((mtrr int) (c int_array) (a int_int_array))" in
  let e1 = expression vars "(max (+ mtrr c#0) \
                            (max (+ mtrr (+ c#0 (+ c#1 (+ a#0#1 a#1#0)))) (+ a#0#1 a#0#0)))" in
  let ctx = make_context vars "((mtrr c) () (a) (mtrr c a) (mtrr c#0 c#1))" in
  let splittin_results =
    (match flatten_AC e1 with
     | FnApp(_, _, el) ->
       __factorize_multi__  ctx Max el
     | _ -> [])
  in
  printf "Split expression:@.%a@." cp_expr_list splittin_results;
  if List.length splittin_results < 1 then
    msg_failed tname
  else
    msg_passed tname

(* A group of normalization tests to ensure we do not 'break' the old examples.
*)
let normalization_test lin name context expr expected =
  let expr_norm = normalize ~linear:lin context expr in
  let normal_expressions = collect_normal_subexpressions context expr_norm in
  printf "Normal subexpressions:@.%a@." cp_expr_list normal_expressions;
  if expected @= expr_norm then
    msg_passed (sprintf "Normalization of %s test passed." name)
  else
    begin
      msg_failed (sprintf "Normalization test of %s failed." name);
      printf "Expected:@.%a@.Result of normalization:@.%a@."
        cp_fnexpr expected
        cp_fnexpr expr_norm
    end


let test_normalize_expression_00 () =
  printf "Test: normalizing expression from second unfolding of \
          max terminal sum.@.";
  let mts0 = make_int_varinfo "mts0" in
  let a = make_int_array_varinfo "a" in
  let a1 = a $ (_ci 1) in
  let a0 = a $ (_ci 0) in
  let mts1 =                    (* max(max(mts0 + a0, 0) + a1, 0) *)
    fmax (fplus (fmax (fplus (evar mts0) a0) sk_zero) a1) sk_zero in
  let ctx =
    {state_vars = VarSet.singleton mts0;
     index_vars = VarSet.empty;
     used_vars = VarSet.singleton a;
     all_vars = VarSet.of_list [mts0; a];
     costly_exprs = ES.of_list [(evar mts0)]}
  in
  let emts1 =                   (* max(mts0 + a1 + a0, max(a1 + 0, 0)) *)
    fmax (fplus (evar mts0) (fplus a0 a1)) (fmax (fplus a1 sk_zero) sk_zero)
  in
  normalization_test false "mts" ctx mts1 emts1

let test_normalize_expression_01 () =
  printf "Test: normalizing expression from second unfolding of \
          max top left rectangle.@.";
  let col0 = make_int_array_varinfo "col0" in
  let mtrl0 = make_int_varinfo "mtrl0" in
  let a = make_int_int_array_varinfo "A" in
  let a01 = (a $$ (_ci 0, _ci 1)) in
  let a11 = (a $$ (_ci 1, _ci 1)) in
  let a10 = (a $$ (_ci 1, _ci 0)) in
  let a00 = (a $$ (_ci 0, _ci 0)) in
  let c0 = (col0 $ (_ci 0)) in
  let c1 = (col0 $ (_ci 1)) in
  let mtrl1 =
    fmax
      (fmax
         (fplus (fplus c0 a00) a10)
         (fplus (fplus c1 a01) a11))
      (fmax
         (evar mtrl0)
         (fmax sk_zero
            (fmax
               (fplus c0 a00)
               (fplus c1 a01))))
  in
  let ctx =
    { state_vars = VarSet.of_list [col0; mtrl0];
      index_vars = VarSet.empty;
      used_vars = VarSet.of_list [a];
      all_vars = VarSet.of_list [col0; mtrl0; a];
      costly_exprs = ES.of_list [evar mtrl0; c0; c1];
    }
  in
  let mtrl1_norm_expected =
    fmax
      (fplus c1 (fmax (fplus a11 a01) a01))
      (fmax
         (fplus c0
            (fmax (fplus a10 a00) a00))
         (fmax (evar mtrl0) (_ci 0)))
  in
  normalization_test true "mtlr" ctx mtrl1 mtrl1_norm_expected


let test_normalize_expression_02 () =
  printf "Test: normalizing expression from second unfolding of \
          max top right rectangle.@.";
  let mtrr0 = make_int_varinfo "mtrr0" in
  let a = make_int_int_array_varinfo "A" in
  let c = make_int_array_varinfo "c" in
  let a00 = a $$ (sk_zero, sk_zero) in
  let a10 = a $$ (sk_one, sk_zero) in
  let a01 = a $$ (sk_zero, sk_one) in
  let a11 = a $$ (sk_one, sk_one) in
  let c0, c1 = c $ sk_zero, c $ sk_one in
  let mtrr1 =
    fmax
      (fmax (evar mtrr0)
         (fmax (fplus (fplus c1 a01) (fplus c0 a00))
            (fplus c0 a00)))
      (fmax (fplus (fplus (fplus c1 a01) a11)
               (fplus (fplus c0 a00) a10))
         (fplus (fplus c0 a00) a10))
  in
  let ctx =
    {
      state_vars = VarSet.of_list [mtrr0; c];
      index_vars = VarSet.empty;
      used_vars = VarSet.singleton a;
      all_vars = VarSet.of_list [mtrr0; a; c];
      costly_exprs = ES.of_list [c0; c1; evar mtrr0]
    }
  in
  let mtrr1_norm_expected =
    (fmax
       (fplus c0 (fplus c1 (fmax (fplus a01 a00)
                              (fplus (fplus a10 a00)
                                 (fplus a11 a01)))))
       (fmax
          (fplus c0 (fmax a00 (fplus a00 a10)))
          (evar mtrr0)))
  in
  normalization_test true "mtrr" ctx mtrr1 mtrr1_norm_expected

let test_normalize_expression_03 () =
  printf "Test: normalizing expression from second unfolding of \
          well-balanced parenthesis.@.";
  let wb0, cnt0 = make_bool_varinfo "wb0", make_int_varinfo "cnt0" in
  let a = make_bool_array_varinfo "A" in
  let a0 = a $ sk_zero in
  let a1 = a $ sk_one in
  let wb1 =
    fand (fand (evar wb0)
            (fgt (fplus (evar cnt0) (_Q a0 sk_one (fneg sk_one))) sk_zero))
      (fgt (fplus (fplus (evar cnt0) (_Q a0 sk_one (fneg sk_one)))
              (_Q a1 sk_one (fneg sk_one))) sk_zero)
  in
  let ctx = {
    state_vars = VarSet.of_list [wb0; cnt0];
    index_vars = VarSet.empty;
    used_vars = VarSet.singleton a;
    all_vars = VarSet.of_list [wb0; cnt0; a];
    costly_exprs = ES.of_list [evar wb0; evar cnt0]
  } in
  let wb1_norm_expected =
    fand
      (fgt
         (fplus (evar cnt0)
            (fmin (_Q a0 sk_one (fneg sk_one))
               (fplus (_Q a0 sk_one (fneg sk_one))
                  (_Q a1 sk_one (fneg sk_one))))) sk_zero)
      (evar wb0)
  in
  normalization_test false "wb" ctx wb1 wb1_norm_expected


let test_normalize_expression_04 () =
  printf "Test: normalizing expression from second unfolding of \
          max top right rectangle (m = 3).@.";
  let mtrr0 = make_int_varinfo "mtrr0" in
  let a = make_int_int_array_varinfo "A" in
  let c = make_int_array_varinfo "c" in
  let a00 = a $$ (sk_zero, sk_zero) in
  let a10 = a $$ (sk_one, sk_zero) in
  let a01 = a $$ (sk_zero, sk_one) in
  let a11 = a $$ (sk_one, sk_one) in
  let a02 = a $$ (sk_zero, (_ci 2)) in
  let a12 = a $$ (sk_one, (_ci 2)) in
  let c0, c1, c2 = c $ sk_zero, c $ sk_one, c $ (_ci 2)in
  let mtrr1 =
    fmax
      (fmax (evar mtrr0)
         (fmax
            (fplus (fplus (fplus c1 a01) (fplus c0 a00)) (fplus c2 a02))
            (fmax
               (fplus (fplus c1 a01) (fplus c0 a00))
               (fplus c0 a00))))

      (fmax
         (fplus (fplus (fplus (fplus c1 a01) a11) (fplus (fplus c0 a00) a10))(fplus (fplus c2 a02) a12))
         (fmax (fplus (fplus (fplus c1 a01) a11) (fplus (fplus c0 a00) a10))
            (fplus (fplus c0 a00) a10)))
  in
  let costly_exprs = [c0; c1; c2; evar mtrr0] in
  let ctx =
    {
      state_vars = VarSet.of_list [mtrr0; c];
      index_vars = VarSet.empty;
      used_vars = VarSet.singleton a;
      all_vars = VarSet.of_list [mtrr0; a; c];
      costly_exprs = ES.of_list costly_exprs
    }
  in
  let mtrr1_norm_expected =
    (fmax
       (fplus c2
          (fplus c0
             (fplus c1
                (fmax
                   (fplus a02
                      (fplus a00 a01))
                   (fplus a12
                      (fplus a02
                         (fplus a10
                            (fplus a00
                               (fplus a11 a01)))))))))
       (fmax
          (fplus c0
             (fplus c1
                (fmax
                   (fplus a10
                      (fplus a00
                         (fplus a11 a01)))
                   (fplus a00 a01))))
          (fmax
             (fplus c0
                (fmax a00
                   (fplus a10 a00)))
             (evar mtrr0))))
  in
  normalization_test true "mtrr2" ctx mtrr1 mtrr1_norm_expected


let test_normalize_expression_05 () =
  printf "Test: two unfolding of maxmimum prefix sum.@.";
  let vars = vardefs "((mps int) (sum int) (a int_array))" in
  let e0 = expression vars "(max (max mps (+ sum a#0)) (+ (+ sum a#0) a#1))" in
  let e1 = expression vars "(max (+ sum (max a#0 (+ a#1 a#0))) mps)" in
  let ctx = { state_vars = VarSet.of_list [vars#get "sum"; vars#get "mps"];
              index_vars = VarSet.empty;
              used_vars = VarSet.singleton (vars#get "a");
              all_vars = VarSet.of_list [vars#get "sum"; vars#get "mps"; vars#get "a"];
              costly_exprs = ES.of_list [evar (vars#get "sum"); evar (vars#get "mps")] }
  in
  normalization_test false "mps" ctx e0 e1

let test_local_normal_test () =
  let tname = "Test local normal." in
  let ploc_res fmt locres =
    fprintf fmt (match locres with
        | NonNormal -> "NonNormalal"
        | Normal -> "Normal"
        | Input -> "Input"
        | State -> "State"
        | Const -> "Const")
  in
  let vars = vardefs "((mps int) (sum int) (c int_array) (a int_array))" in
  let expr0 = List.map (expression vars)
      ["(+ a#0 a#1)";
       "(max (- sum c#0) c#22)";
       "(+ (+ mps sum) (+ a#0 (+ a#1 a#2)))";
       "(+ (+ mps (+ sum c#0)) (+ a#0 (+ a#1 a#2)))";
       "(+ (+ (+ mps a#0) (+ sum c#0)) (+ a#0 (+ a#1 a#2)))";
       "(max (+ mps (max c#0 c#1)) (+ a#0 a#1))"]
  in
  let ctx = make_context vars
      "((mps sum c) () (a) (mps sum c a) (mps sum c#0))"
  in
  let loc_res =
    List.map (locality_rule ctx) expr0
  in
  let expected_list =
    [Input; State; Normal; Normal; NonNormal; Normal]
  in
  if loc_res = expected_list then
    msg_passed tname
  else
    (List.iter
       (fun (r, e) ->
          printf "Expression %a is %a.@." cp_fnexpr e ploc_res r
       )
       (ListTools.pair loc_res expr0);
     msg_failed tname)


let test () =
  test_flatten_expression ();
  test_split_expression ();
  test_normalize_expression_01 ();
  test_normalize_expression_00 ();
  test_normalize_expression_02 ();
  test_normalize_expression_03 ();
  test_normalize_expression_04 ();
  test_normalize_expression_05 ();
  test_local_normal_test ()
