open SymbExe
open Utils
open Cil
open TestUtils

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
