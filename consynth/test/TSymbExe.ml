open SymbExe
open Utils
open Cil
open TestUtils
open SPretty
open ExpressionReduction

module T = SketchTypes


let x, y, z =
  T.SkVarinfo (make_int_varinfo "x"),
  T.SkVarinfo (make_int_varinfo ~init:one "y"),
  T.SkVarinfo (make_int_varinfo "z")

let a, b, c =
  T.SkVarinfo (make_bool_varinfo "a"),
  T.SkVarinfo (make_bool_varinfo ~init:cil_false "b"),
  T.SkVarinfo (make_bool_varinfo "c")

let f_a_plus_b =
  (T.SkLetIn ([(a, T.SkBinop (T.Plus, T.SkVar b, T.SkVar a))], sk_tail_state))

let g =
  (T.SkLetIn ([a, T.SkBinop (T.Max, T.SkVar a, T.SkVar c)], f_a_plus_b))

let index_var = make_int_varinfo "i"
let index_expr = exp_skvar index_var
let array = T.SkArray (c, index_expr)

let a_vi = check_option (vi_of_var a)
let stv = VS.singleton a_vi
let init_exprs = IM.singleton a_vi.vid (exp_skvar a_vi)

let sum_array =
  (T.SkLetIn ([a,
               T.SkBinop(T.Max,
                         sk_zero,
                         T.SkBinop (T.Plus, T.SkVar a, T.SkVar array))],
             sk_tail_state))

let increment_all_indexes index_exprs =
  IM.fold
    (fun vid expr ->
       IM.add vid (T.SkBinop (T.Plus, expr, sk_one))
    )
    index_exprs
    IM.empty
let index_map1 = IM.singleton index_var.vid index_expr
let index_map2 = increment_all_indexes index_map1
let index_map3 = increment_all_indexes index_map2
(** Apply the functions to states *)
let index_set = VS.singleton index_var

let r1 = exec_once ~index_set:index_set ~index_exprs:index_map1 stv init_exprs g

let r2 = exec_once ~index_set:index_set ~index_exprs:index_map2 stv r1 g

let r1_array =
  exec_once ~index_set:index_set ~index_exprs:index_map1
    stv init_exprs sum_array


let r2_array = exec_once ~index_set:index_set ~index_exprs:index_map1
    stv r1_array sum_array

let reduced_r2_array = IM.map (cost_reduce stv) r2_array

let print_exprs str exprs =
  Format.printf "%s :\n" str;
  IM.iter
    (fun vid expr -> Format.printf "%i : %a\n" vid pp_skexpr expr)
    exprs

let test () =
  print_exprs "r1" r1;
  print_exprs "r2" r2;
  print_exprs "r1_array" r1_array;
  print_exprs "r2_array" r2_array;
  print_exprs "red_r2_array" reduced_r2_array
