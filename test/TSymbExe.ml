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
open Format


type stv_type =
  | Scalar of constants
  | Linear of (int * constants) list

let symbolic_execution_test tname vars ctx funct unfoldings efinal =
  let indexes =  create_symbol_map ctx.index_vars in
  let state = create_symbol_map ctx.state_vars in
  let xinfo =
    {
      context = ctx;
      state_exprs = state;
      index_exprs = indexes;
      inputs = ES.empty;
    }
  in
  let results, inputs = unfold_once ~silent:false xinfo funct in
  try
    List.iter
      (fun (vid, stv_type) ->
         let e = IM.find vid results in
         match stv_type, e with
         | Scalar c, FnConst c' -> if c = c' then () else failwith "Y"
         | Linear kl, FnVector ar ->
           (List.iter
              (fun (k, c) ->
                 if FnConst c = Array.get ar k then () else failwith "X") kl)
         | _ -> failwith "Z")
      efinal;
    msg_passed ("Test passed: "^tname)
  with Failure s ->
    IM.iter
      (fun k e -> printf "%a@." cp_fnexpr e) results;
    msg_failed (tname^" : "^s)


let test_01 () =
  let vars = vardefs "((sum int) (i int) (c int_array) (A int_array))" in
  let cont = make_context vars "((sum c) (i) (A) (sum c i A) (sum c))" in
  let c = vars#get "c" in
  let sum = vars#get "sum" in
  let funct =
    _letin
      [(FnArray (FnVariable c, sk_zero), sk_zero);
       (FnVariable sum, sk_zero)]
      (_letin [(FnArray (FnVariable c, sk_one)), (FnVar (FnArray (FnVariable c, sk_zero)))]
         sk_tail_state)
  in
  symbolic_execution_test "sum0" vars cont funct 1
    [(sum.vid, Scalar (CInt 0));(c.vid, Linear [(0, CInt 0); (1,CInt 0)])]



let test_02 () =
  let vars = vardefs "((sum int) (i int) (c int_array) (A int_array))" in
  let cont = make_context vars "((sum c) (i) (A) (sum c i A) (sum c))" in
  let c = vars#get "c" in
  let sum = vars#get "sum" in
  let i = vars#get "i" in
  let funct =
    _letin
      [(FnArray (FnVariable c, sk_zero), sk_zero);
       (FnVariable sum, sk_zero)]
      (_letin [(FnArray (FnVariable c, sk_one)), (FnVar (FnArray (FnVariable c, sk_zero)))]
         (_let [(FnArray (FnVariable c, _ci 2)),
                  (FnRec (
                      (* Initial value, guard and update of index of the loop. *)
                    (_ci 0, (flt (evar i) (_ci 10)),(fplus (evar i) sk_one)),
                    (* Initial state *)
                    (VarSet.empty, (FnLetExpr [])),
                      (* Body of the loop *)
                         (c, (_let [(FnArray (FnVariable c, _ci 2)), _ci 2]))))]))
  in
  symbolic_execution_test "sum1" vars cont funct 1
    [(sum.vid, Scalar (CInt 0));(c.vid, Linear [(0, CInt 0); (1,CInt 0); (2, CInt 2)])]

let test_03 () =
  (* TODO: partial execution for indexes (partial exec for integers) *)
  let vars = vardefs "((sum int) (i int) (c int_array) (A int_array))" in
  let cont = make_context vars "((sum c) (i) (A) (sum c i A) (sum c))" in
  let c = vars#get "c" in
  let sum = vars#get "sum" in
  let i = vars#get "i" in
  let funct =
    _letin
      [(FnArray (FnVariable c, sk_zero), sk_zero);
       (FnVariable sum, sk_zero)]
      (_letin [(FnArray (FnVariable c, sk_one)), (FnVar (FnArray (FnVariable c, sk_zero)));
               (FnArray (FnVariable c, _ci 2)), (FnVar (FnArray (FnVariable c, sk_zero)))]
         (_let [(FnArray (FnVariable c, _ci 2)),
                  (FnRec (
                      (* Initial value, guard and update of index of the loop. *)
                    (_ci 0, (flt (evar i) (_ci 10)),(fplus (evar i) sk_one)),
                    (* Initial state *)
                    (VarSet.empty, FnLetExpr([])),
                      (* Body of the loop *)
                    (c, (_let [(FnArray (FnVariable c, _ci 2)),
                             (fplus (FnVar (FnArray (FnVariable c, _ci 2))) sk_one)]))))]))
  in
  symbolic_execution_test "sum2" vars cont funct 1
    [(sum.vid, Scalar (CInt 0));(c.vid, Linear [(0, CInt 0); (1,CInt 0); (2, CInt 10)])]


(* Normalization: file defined tests. *)
let test_load filename =
  let inchan = IO.input_channel (open_in filename) in
  let message = IO.read_line inchan in
  print_endline message;

  (* let title = IO.read_line inchan in
   * let unfoldings = int_of_string (IO.read_line inchan) in
   * let vars = vardefs (IO.read_line inchan) in
   * let context = make_context vars (IO.read_line inchan) in
   * let funct = expression vars (IO.read_line inchan) in
   * let efinal = expression vars (IO.read_line inchan) in *)
  ()

let file_defined_tests () =
  let test_files =
    glob (Conf.project_dir^"/test/symbolic_execution/*.test")
  in
  List.iter test_load test_files



let test () =
  test_01 ();
  test_02 ();
  test_03 ();
  file_defined_tests ()
