open SymbExe
open Utils
open Cil
open TestUtils
open SPretty

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

let index_expr = exp_skvar (make_int_varinfo "i")
let array = T.SkArray (a, index_expr)

let a_vi = check_option (vi_of_var a)
let stv = VS.singleton a_vi
let init_exprs = IM.singleton a_vi.vid (exp_skvar a_vi)

let r1 = exec_once stv init_exprs g index_expr
let r2 = exec_once stv r1 g index_expr

let print_exprs str exprs =
  Format.printf "%s :\n" str;
  IM.iter
    (fun vid expr -> Format.printf "%i : %a\n" vid pp_skexpr expr)
    exprs

let test () =
  print_exprs "r1" r1;
  print_exprs "r2" r2
