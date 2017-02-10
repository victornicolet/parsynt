open Format
open SymbExe
open Utils
open Cil
open TestUtils
open SPretty
open ExpressionReduction
open Expressions
open VariableDiscovery

open SketchTypes

let x, y, z, a, b, c, a_n =
  SkVarinfo (make_int_varinfo "x"),
  SkVarinfo (make_int_varinfo ~init:one "y"),
  SkVarinfo (make_int_varinfo "z"),
  SkVarinfo (make_int_varinfo "a"),
  SkVarinfo (make_bool_varinfo ~init:cil_false "b"),
  SkVarinfo (make_bool_varinfo "c"),
  SkVarinfo (make_int_array_varinfo "a_n")


let e_1 =
  SkBinop (Plus, SkBinop (Plus, SkVar x , SkVar y),
           SkBinop (Plus, SkVar a,SkVar  b))

let e_1_flat = flatten_AC e_1


let e_2 =
  SkBinop (Times, e_1, SkBinop (Times, SkVar x, SkUnop (Neg, SkVar y)))

let e_2_flat = flatten_AC e_2
;;

printf "e_1 = %a @. e_1_flat = %a@." pp_skexpr e_1 pp_skexpr e_1_flat;
printf "e_2 = %a @. e_2_flat = %a@." pp_skexpr e_2 pp_skexpr e_2_flat
