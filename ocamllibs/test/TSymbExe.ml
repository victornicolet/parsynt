(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
  *)

open SymbExe
open Utils
open Cil
open TestUtils
open ExpressionReduction
open VariableDiscovery
open FPretty
open FuncTypes


let x, y, z, a, b, c, a_n =
  (make_int_varinfo "x"),
  (make_int_varinfo ~init:one "y"),
  (make_int_varinfo "z"),
  (make_int_varinfo "a"),
  (make_bool_varinfo ~init:cil_false "b"),
  (make_bool_varinfo "c"),
  (make_int_array_varinfo "a_n")

let index_var = make_int_varinfo "i"
let index_expr = mkVarExpr index_var
let array = FnArray (FnVarinfo a_n, index_expr)

let allvs  = VS.of_list [x; y; z; a; b; c; a_n; index_var]

let stv = VS.singleton a

let sctx : context =
    { state_vars = stv;
      index_vars = VS.singleton index_var;
      all_vars = allvs;
      used_vars = allvs;
      costly_exprs = ES.empty;
    }

let init_exprs = IM.singleton a.vid (mkVarExpr a)

let skv_a = FnVarinfo a
let sum_array =
  (FnLetIn ([skv_a,
             FnBinop(Max,
                         sk_zero,
                         FnBinop (Plus, FnVar skv_a, FnVar array))],
             sk_tail_state))


let index_map1 = IM.singleton index_var.vid index_expr
let index_map2 = increment_all_indexes index_map1
let index_map3 = increment_all_indexes index_map2
(** Apply the functions to states *)
let index_set = VS.singleton index_var

let r0 : exec_info = { context = sctx;
           state_exprs = init_exprs;
           index_exprs = index_map1;
           inputs = ES.empty
         }

let r1_array = GenVars.init () ;
  let sexprs, rexprs = unfold_once r0 sum_array in
  { r0 with state_exprs = sexprs;
            inputs = rexprs;
            index_exprs = index_map2 }

let r2_array =
  let r2ae, r2ar =
    unfold_once {r1_array with inputs = ES.empty} sum_array
  in
  { r1_array with state_exprs = r2ae;
                               inputs = r2ar;
                               index_exprs = index_map3 }



let reduced_r2_array = IM.map (reduce_full sctx)
    r2_array.state_exprs

let print_exprs str exprs =
  Format.printf "%s :\n" str;
  IM.iter
    (fun vid expr -> Format.printf "%i : %a\n" vid pp_fnexpr expr)
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
