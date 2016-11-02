open Format
open SPretty
open Expressions
open ExpressionReduction
open Utils
open TestUtils
open SketchTypes

let main () =
  (** Create all necessary variables *)
  let mssvi, mtsvi, avi, ivi, nvi, auxvi =
    make_int_varinfo "mss",
    make_int_varinfo "mts",
    make_int_array_varinfo "a",
    make_int_varinfo "i",
    make_int_varinfo "n",
    make_int_varinfo "aux"
  in
  let mss, mts, a, i, n, aux =
    SkVarinfo mssvi,
    SkVarinfo mtsvi,
    SkVarinfo avi,
    SkVarinfo ivi,
    SkVarinfo nvi,
    SkVarinfo auxvi
  in
  let stv = VS.of_list [mssvi; mtsvi] in
  (* let index_set = VS.singleton ivi in *)
  let i1 =
    SkBinop (Plus, SkVar i, sk_one)
  in
  (* let i2 = *)
  (*   SkBinop (Plus, i1, sk_one) *)
  (* in *)
  (* let i3 = *)
  (*   SkBinop (Plus, i2, sk_one) *)
  (* in *)
  let e1 =  SkBinop (Plus, SkVar mts, SkVar (SkArray (a, SkVar i))) in
  let a_i =  SkVar (SkArray (a, SkVar i)) in
  let a_i_1 = SkVar (SkArray (a, i1)) in
  let e_zero = sk_zero in
  let cst_e1 = (cost stv ES.empty e1) in
  let cst_a_i_1 = (cost stv ES.empty a_i_1) in
  let cst_zero =  (cost stv ES.empty e_zero) in

  printf "@.Cost of e1 = %a : (%i, %i)@."
    pp_skexpr e1 (fst cst_e1) (snd cst_e1);
  printf "@.Cost of a_i_1 = %a : (%i, %i)@." pp_skexpr a_i_1
    (fst cst_a_i_1) (snd cst_a_i_1);
  printf "@.Cost of e_zero = %a : (%i, %i)@." pp_skexpr e_zero
    (fst cst_zero) (snd cst_zero);
  printf "@.Distributivity condition : %B@."
    (is_right_distributive Max Plus && (max cst_e1 cst_zero) >= cst_a_i_1);

  (** SPecific test on the annoying expression *)
  let failing_expression =  SkBinop (Plus, SkBinop (Max, e1, e_zero), a_i_1) in

  let e2 =  SkBinop (Plus, SkVar (SkArray (a, SkVar i)), SkVar mts) in
  let mss_full =
    SkBinop (Max,
             failing_expression,
             SkBinop (Max, e2, SkVar mss)) in
  printf "@.Expression before reduction :@.%a@." pp_skexpr mss_full;
  let mss_full_red = reduce_full stv ES.empty mss_full in
  printf "@.Apply full reduction :@.%a@." pp_skexpr mss_full_red;
  printf "@.Replace %a by %a.@." pp_skexpr (SkBinop (Plus, a_i, a_i_1))
    pp_skexpr       (SkVar aux);
  let replaced = replace_AC (stv, ES.empty)
      (SkBinop (Max, (SkBinop (Plus, a_i, a_i_1)), a_i))
      (SkVar aux)
      mss_full_red
  in
  printf "After replacement operation : %a@." pp_skexpr replaced;;


main ()
