open Cil
open Format
open SPretty
open Utils
open VariableDiscovery
open TestUtils

module T = SketchTypes

(** Counting blocks of one example *)
let n_vi, n, n_e =
  let vi = make_int_varinfo "N" in
  (vi, T.mkVar vi, T.mkVarExpr vi);;

(** Index var *)
let i_vi, i, i_e =
  let vi = make_int_varinfo "ind" in
  (vi, T.mkVar vi, T.mkVarExpr vi);;

let i_set, i_map = VS.singleton i_vi, IM.singleton i_vi.vid i_e ;;

let sigu = i_set, (T.SkLetExpr [(i, (T.SkConst (T.CInt 0)))],
                   T.SkBinop (T.Lt, i_e, n_e),
                   T.SkLetExpr [(i, T.SkBinop (T.Plus, i_e, sk_one))]);;



(** Input array *)
let a_vi, a, a_e =
  let vi = make_int_varinfo "array" in
  vi, T.mkVar ~offsets:[i_e] vi, T.mkVarExpr ~offsets:[i_e] vi

(** State variables : a flag and a counter *)

let f_vi, f, f_e =
  let vi = make_bool_varinfo "flag" in
  (vi, T.mkVar vi, T.mkVarExpr vi)

let count_vi, count, count_e =
  let vi = make_int_varinfo "count" in
  vi, T.mkVar vi, T.mkVarExpr vi


let state = VS.of_list [f_vi; count_vi];;



(** Function *)
let counting_block =
  T.SkLetExpr [(f, a_e);
             (count,
              T.SkBinop(T.Plus,
                      count_e,
                      T.SkQuestion(
                        T.SkBinop(T.And, T.SkUnop(T.Not, f_e), a_e),
                        sk_one,
                        sk_zero)))]



let test () =
  let new_state, new_func =
      discover state counting_block sigu
  in
  fprintf std_formatter
    "New state is : %a@. New function is : @.%a"
    VSOps.pvs new_state pp_sklet new_func;;
