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

let f_a_plus_b =
  (T.SkLetIn ([(a, T.SkBinop (T.Plus, T.SkVar b, T.SkVar a))], sk_tail_state))

let g =
  (T.SkLetIn ([a, T.SkBinop (T.Max, T.SkVar a, T.SkVar c)], f_a_plus_b))

let index_var = make_int_varinfo "i"
let index_expr = exp_skvar index_var
let array = T.SkArray (a_n, index_expr)

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

let r0 = { state_set = stv; state_exprs = init_exprs;
           index_set = index_set; index_exprs = index_map1}

let r1 = {r0 with state_exprs = exec_once r0 g;
                  index_exprs = index_map2;}

let r2 = exec_once r1 g

let r1_array = init () ;
  { r0 with state_exprs = exec_once r0 sum_array;
            index_exprs = index_map2 }


let r2_array = { r1_array with state_exprs = exec_once r1_array sum_array;
                         index_exprs = index_map3 }


let reduced_r2_array = IM.map (reduce_full stv) r2_array.state_exprs

let print_exprs str exprs =
  Format.printf "%s :\n" str;
  IM.iter
    (fun vid expr -> Format.printf "%i : %a\n" vid pp_skexpr expr)
    exprs

let test () =
  print_exprs "r1" r1.state_exprs;
  print_exprs "r2" r2;
  print_exprs "r1_array" r1_array.state_exprs;
  print_exprs "r2_array" r2_array.state_exprs;
  print_exprs "red_r2_array" reduced_r2_array;
  Format.printf "Find accumulator between r1_array and reduced_r2_array.@.";
  let decl_vars = declared_vars () in
  VSOps.ppvs decl_vars;
  find_function (VSOps.unions [stv; decl_vars; index_set]) (IM.find a_vi.vid reduced_r2_array)
    (IM.find a_vi.vid r1_array.state_exprs)

(** Test variable discovery algortihm *)
let index_incr =
  T.SkLetExpr ([T.SkVarinfo index_var,
               (T.SkBinop (T.Plus, T.SkVar (T.SkVarinfo index_var), sk_one))])

let index_init =
  T.SkLetExpr ([T.SkVarinfo index_var, sk_zero])

let index_guard =
  T.SkBinop (T.Le, T.SkVar (T.SkVarinfo index_var), T.SkConst (T.CInt 10))

let igu = (index_init, index_guard, index_incr)

let discovered, newfunc = discover stv sum_array (index_set, igu)

let test2 () =
  VS.iter (fun vi -> Format.printf "New variable : %s@." vi.vname) discovered;
  Format.printf "New function :@.%a@." pp_sklet newfunc
