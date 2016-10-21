open SymbExe
open Utils
open Cil
open TestUtils
open SPretty
open ExpressionReduction
open VariableDiscovery

module T = SketchTypes


let x, y, z, a, b, c, a_n =
  T.SkVarinfo (make_int_varinfo "x"),
  T.SkVarinfo (make_int_varinfo ~init:one "y"),
  T.SkVarinfo (make_int_varinfo "z"),
  T.SkVarinfo (make_int_varinfo "a"),
  T.SkVarinfo (make_bool_varinfo ~init:cil_false "b"),
  T.SkVarinfo (make_bool_varinfo "c"),
  T.SkVarinfo (make_int_array_varinfo "a_n")

let index_var = make_int_varinfo "i"
let index_expr = T.mkVarExpr index_var
let array = T.SkArray (a_n, index_expr)

let a_vi = check_option (vi_of_var a)
let stv = VS.singleton a_vi
let init_exprs = IM.singleton a_vi.vid (T.mkVarExpr a_vi)

let sum_array =
  (T.SkLetIn ([a,
               T.SkBinop(T.Max,
                         sk_zero,
                         T.SkBinop (T.Plus, T.SkVar a, T.SkVar array))],
             sk_tail_state))


let index_map1 = IM.singleton index_var.vid index_expr
let index_map2 = increment_all_indexes index_map1
let index_map3 = increment_all_indexes index_map2
(** Apply the functions to states *)
let index_set = VS.singleton index_var

let r0 = { state_set = stv; state_exprs = init_exprs;
           index_set = index_set; index_exprs = index_map1;
           inputs = SketchTypes.ES.empty
         }

let r1_array = GenVars.init () ;
  let sexprs, rexprs = exec_once r0 sum_array in
  { r0 with state_exprs = sexprs;
            inputs = rexprs;
            index_exprs = index_map2 }

let r2_array =
  let r2ae, r2ar =
    exec_once {r1_array with inputs = SketchTypes.ES.empty} sum_array
  in
  { r1_array with state_exprs = r2ae;
                               inputs = r2ar;
                               index_exprs = index_map3 }

let reduced_r2_array = IM.map (reduce_full stv SketchTypes.ES.empty)
    r2_array.state_exprs

let print_exprs str exprs =
  Format.printf "%s :\n" str;
  IM.iter
    (fun vid expr -> Format.printf "%i : %a\n" vid pp_skexpr expr)
    exprs

let test () =
  print_exprs "r1_array" r1_array.state_exprs;
  Format.fprintf Format.std_formatter
    "Inputs at first iteration :@.%a@.@."
    (fun fmt es ->  pp_expr_set fmt es) r1_array.inputs;
  print_exprs "r2_array" r2_array.state_exprs;
  Format.fprintf Format.std_formatter
    "Inputs at second iteration :@.%a@.@."
    (fun fmt es ->  pp_expr_set fmt es) r2_array.inputs;
  print_exprs "red_r2_array" reduced_r2_array
