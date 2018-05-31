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

open Beta
open SymbExe
open Utils
open TestUtils
open ExpressionReduction
open VariableDiscovery
open FPretty
open FuncTypes
open Format


type stv_type =
  | SymbScalar of fnExpr
  | Scalar of constants
  | Linear of (int * constants) list
  | SymbLinear of (int * fnExpr) list

let symbolic_execution_test ?(_xinfo = None) tname vars ctx funct unfoldings efinal =
  let indexes =  create_symbol_map ctx.index_vars in
  let state = create_symbol_map ctx.state_vars in
  let xinfo =
    match _xinfo with
    | None ->
      {
        context = ctx;
        state_exprs = state;
        index_exprs = indexes;
        inputs = ES.empty;
      }
    | Some xinfo -> xinfo
  in
  let results, inputs = unfold_once ~silent:false xinfo funct in
  begin
    try
      List.iter
        (fun (vid, stv_type) ->
           let e = IM.find vid results in
           match stv_type, e with
           | Scalar c, FnConst c' -> if c = c' then () else failwith "Y"
           | SymbScalar sc, e -> if e = sc then () else failwith "YY"
           | Linear kl, FnVector ar ->
             (List.iter
                (fun (k, c) ->
                   if FnConst c = List.nth ar k then () else failwith "X") kl)
           | SymbLinear skl, FnVector ar ->
             (List.iter
                (fun (k, c) ->
                   if c = List.nth ar k then () else failwith "X") skl)
           | _ -> failwith "failed")
        efinal;
      msg_passed ("Test passed: "^tname)
    with Failure s ->
      IM.iter
        (fun k e -> printf "@[<v 2>%s : %a =@;%a@]@."
            (VarSet.find_by_id ctx.state_vars k).vname
            pp_typ (type_of e) cp_fnexpr e ) results;
      msg_failed (tname^" : "^s)
  end;
  results

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
  ignore(symbolic_execution_test "sum0" vars cont funct 1
           [(sum.vid, Scalar (CInt 0));(c.vid, Linear [(0, CInt 0); (1,CInt 0)])])



let test_02 () =
  let vars = vardefs "((sum int) (i int) (c int_array) (A int_array))" in
  let cont = make_context vars "((sum c) (i) (A) (sum c i A) (sum c))" in
  let c = vars#get "c" in
  let sum = vars#get "sum" in
  let i = vars#get "i" in
  let inloop_state = VarSet.singleton c in
  let inloop_type = Record(VarSet.record inloop_state) in
  let state_binder = mkFnVar "_st" inloop_type in
  let tup = mkFnVar "tup" inloop_type in
  let funct =
    _letin
      [(FnArray (FnVariable c, sk_zero), sk_zero);
       (FnVariable sum, sk_zero)]
      (_letin [FnArray (var c, sk_one),  c $ sk_zero]
         (_letin [var tup,
                  (FnRec (
                      (* Initial value, guard and update of index of the loop. *)
                      (_ci 0, (flt (evar i) (_ci 10)),(fplus (evar i) sk_one)),
                      (* Initial state *)
                      (inloop_state, FnRecord(inloop_type, [evar c])),
                      (* Body of the loop *)
                      (state_binder,
                       (_letin [_self state_binder c]
                          (_letin [(FnArray (var c, _ci 2)), _ci 2]
                             (_let [var c, evar c]))))))]
            (_let [_self tup c])))
  in
  ignore(symbolic_execution_test "sum1" vars cont funct 1
           [(sum.vid, Scalar (CInt 0));(c.vid, Linear [(0, CInt 0); (1,CInt 0); (2, CInt 2)])])

let test_03 () =
  (* TODO: partial execution for indexes (partial exec for integers) *)
  let vars = vardefs "((sum int) (i int) (c int_array) (A int_array))" in
  let cont = make_context vars "((sum c) (i) (A) (sum c i A) (sum c))" in
  let c = vars#get "c" in
  let sum = vars#get "sum" in
  let i = vars#get "i" in
  let inst = VarSet.singleton c in
  let instt = Record (VarSet.record inst) in
  let xs = mkFnVar "xs" instt in
  let funct =
    _letin
      [(FnArray (FnVariable c, sk_zero), sk_zero);
       (FnVariable sum, sk_zero)]
      (_letin [(FnArray (FnVariable c, sk_one)), (FnVar (FnArray (FnVariable c, sk_zero)));
               (FnArray (FnVariable c, _ci 2)), (FnVar (FnArray (FnVariable c, sk_zero)))]
         (_let [FnVariable c,
                (FnRecordMember
                   (FnRec
                      (
                        (* Initial value, guard and update of index of the loop. *)
                        (_ci 0, (flt (evar i) (_ci 10)),(fplus (evar i) sk_one)),
                        (* Initial state *)
                        (inst, FnRecord(instt, [evar c])),
                        (* Body of the loop *)
                        (xs, (_letin [_self xs c]
                                (_letin [FnArray (var c,  _ci 2),
                                         fplus (c $ (_ci 2)) sk_one]
                                   (_let [var c, evar c]))))), c.vname))]))
  in
  let r1 =
    symbolic_execution_test "sum2" vars cont funct 1
      [(sum.vid, Scalar (CInt 0));(c.vid, Linear [(0, CInt 0); (1,CInt 0); (2, CInt 10)])]
  in
  let exec_start_env =
    {
      context = cont;
      state_exprs = r1;
      index_exprs = increment_all_indexes (create_symbol_map cont.index_vars);
      inputs = ES.empty;
    }
  in
  let _ =
    symbolic_execution_test
      ~_xinfo:(Some exec_start_env)
      "sum2, second unfoding" vars cont funct 1
      [(sum.vid, Scalar (CInt 0));(c.vid, Linear [(0, CInt 0); (1,CInt 0); (2, CInt 10)])]
  in
  ()

let test_03bis () =
  (* TODO: partial execution for indexes (partial exec for integers) *)
  let vars = vardefs "((sum int) (i int) (A int_array))" in
  let cont = make_context vars "((sum) (i) (A) (sum i A) (sum ))" in
  let sum = vars#get "sum" in
  let i = vars#get "i" in
  let a = vars#get "A" in
  let inst = VarSet.singleton sum in
  let instt = Record (VarSet.record inst) in
  let xs = mkFnVar "xs" instt in
  let tup = mkFnVar "tup" instt in
  let funct =
    (_letin
       [var tup,
        (FnRec
           (
             (* Initial value, guard and update of index of the loop. *)
             (_ci 0, (flt (evar i) (_ci 4)),(fplus (evar i) sk_one)),
             (* Initial state *)
             (inst, FnRecord(instt, [evar sum])),
             (* Body of the loop *)
             (xs, (_letin [_self xs sum]
                     (_let [var sum, fplus (a $ (evar i)) (evar sum)])))))]
       (_let [_self tup sum]))
  in
  let _ =
    symbolic_execution_test "sum3" vars cont funct 1
      [sum.vid,
       SymbScalar
         (fplus (a $ (_ci 3))
            (fplus (a $ (_ci 2))
               (fplus (a $ (_ci 1))
                  (fplus (a $ (_ci 0)) (evar sum)))))]
  in
  ()

let test_03ter () =
  (* TODO: partial execution for indexes (partial exec for integers) *)
  let vars = vardefs "((sum int) (i int) (j int) (A int_int_array))" in
  let cont = make_context vars "((sum) (i) (A) (sum j i A) (sum ))" in
  let sum = vars#get "sum" in
  let i = vars#get "i" in
  let j = vars#get "j" in
  let a = vars#get "A" in
  let inst = VarSet.singleton sum in
  let instt = Record (VarSet.record inst) in
  let xs = mkFnVar "xs" instt in
  let tup = mkFnVar "tup" instt in
  let funct =
    (_letin
       [var tup,
        (FnRec
           (
             (* Initial value, guard and update of index of the loop. *)
             (_ci 0, (flt (evar j) (_ci 4)), (fplus (evar j) sk_one)),
             (* Initial state *)
             (inst, FnRecord(instt, [evar sum])),
             (* Body of the loop *)
             (xs, (_letin [_self xs sum]
                     (_let [var sum, fplus (a $$ (evar i, evar j)) (evar sum)])))))]
       (_let [_self tup sum]))
  in
  let r1 =
    symbolic_execution_test "sum4" vars cont funct 1
      [sum.vid,
       SymbScalar
         (fplus (a $$ (evar i, _ci 3))
            (fplus (a $$ (evar i, _ci 2))
               (fplus (a $$ (evar i, _ci 1))
                  (fplus (a $$ (evar i, _ci 0)) (evar sum)))))]
  in
  let exec_start_env =
    {
      context = cont;
      state_exprs = r1;
      index_exprs = increment_all_indexes (create_symbol_map cont.index_vars);
      inputs = ES.empty;
    }
  in
  let r2 =
    symbolic_execution_test
      ~_xinfo:(Some exec_start_env)
      "sum4, second unfolding" vars cont funct 1
      [sum.vid,
       SymbScalar
         (fplus (a $$ (fplus (evar i) sk_one, _ci 3))
            (fplus (a $$ (fplus (evar i) sk_one, _ci 2))
               (fplus (a $$ (fplus (evar i) sk_one, _ci 1))
                  (fplus (a $$ (fplus (evar i) sk_one, _ci 0))
                     (fplus (a $$ (evar i, _ci 3))
                        (fplus (a $$ (evar i, _ci 2))
                           (fplus (a $$ (evar i, _ci 1))
                              (fplus (a $$ (evar i, _ci 0)) (evar sum)))))))))]
  in
  let exec_start_env =
    {
      context = cont;
      state_exprs = r2;
      index_exprs =
        increment_all_indexes
          (increment_all_indexes
             (create_symbol_map cont.index_vars));
      inputs = ES.empty;
    }
  in
  let ip1 = fplus (evar i) sk_one in
  let _ =
    symbolic_execution_test
      ~_xinfo:(Some exec_start_env)
      "sum4, third unfolding" vars cont funct 1
      [sum.vid,
       SymbScalar
         (fplus (a $$ (fplus ip1 sk_one, _ci 3))
            (fplus (a $$ (fplus ip1 sk_one, _ci 2))
               (fplus (a $$ (fplus ip1 sk_one, _ci 1))
                  (fplus (a $$ (fplus ip1 sk_one, _ci 0))
                     (fplus (a $$ (ip1, _ci 3))
                        (fplus (a $$ (ip1, _ci 2))
                           (fplus (a $$ (ip1, _ci 1))
                              (fplus (a $$ (ip1, _ci 0))
                                 (fplus (a $$ (evar i, _ci 3))
                                    (fplus (a $$ (evar i, _ci 2))
                                       (fplus (a $$ (evar i, _ci 1))
                                          (fplus (a $$ (evar i, _ci 0)) (evar sum)
                                          ))))))))))))]
  in
  ()


let test_04 () =
  SymbExe.verbose := true;
  let vars = vardefs "((sum int) (mtr int) (c int_array) (mtrl int) (a int_int_array) (i int) (j int))" in
  let cont = make_context vars "((sum mtr mtrl c) (i) (a) (sum mtr mtrl c i j a) (sum mtr mtrl c))" in
  let c = vars#get "c" in let mtr = vars#get "mtr" in let mtrl = vars#get "mtrl" in
  let a = vars#get "a" in let sum = vars#get "sum" in
  let j = vars#get "j" in let i = vars#get "i" in
  let inctx = make_context vars "((sum mtr c) (j) (a) (sum mtr mtrl c j a) (sum mtr c))" in
  let intype = Record (VarSet.record inctx.state_vars) in
  let tup = mkFnVar "tup" intype in
  let bnds = mkFnVar "bound" intype in
  let func =
    (_letin [FnVariable tup,
             FnRec((sk_zero, (flt (evar i) (_ci 5)), (fplus (evar j) sk_one)),
                   (inctx.state_vars, FnRecord(intype, [sk_zero; sk_zero; evar c])),
                   (bnds,
                    (_letin [_self bnds sum; _self bnds mtr; _self bnds c]
                       (_letin [var sum, fplus (a $$ (evar i, evar j)) (evar sum)]
                          (_letin [var c, FnArraySet(evar c, evar j, (fplus (c $ (evar j)) (evar sum)))]
                             (_let [var c, evar c;
                                    var mtr, fmax (c $ (evar j)) (evar mtr);
                                    var sum, evar sum]))))))]
       (_let [_self tup c;
              _self tup mtr;
              var mtrl, fmax (evar mtrl) (_inrec tup mtr);
              _self tup sum]))
  in
  let r1 =
    symbolic_execution_test "mtrl" vars cont func 2
      [sum.vid,
       SymbScalar
         (fplus  (a $$ (evar i, _ci 4))
            (fplus (a $$ (evar i, _ci 3))
               (fplus  (a $$ (evar i, _ci 2))
                  (fplus (a $$ (evar i, _ci 1))
                     (a $$ (evar i, _ci 0))))));
       c.vid,
       SymbLinear [
         0, (fplus (c $ (_ci 0))
               (a $$ (evar i, _ci 0)));
         1, (fplus (c $ (_ci 1))
               (fplus  (a $$ (evar i, _ci 1))
                  (a $$ (evar i, _ci 0))));
       ]]
  in
  let _ =
    let iplus1 = fplus (evar i) sk_one in
    symbolic_execution_test
      ~_xinfo:
        (Some {
            context = cont;
            state_exprs = r1;
            index_exprs = increment_all_indexes (create_symbol_map cont.index_vars);
            inputs = ES.empty;
          })
      "mtrl, second unfolding" vars cont func 2
      [sum.vid,
       SymbScalar
         (fplus  (a $$ (fplus (evar i) sk_one, _ci 4))
            (fplus (a $$ (fplus (evar i) sk_one, _ci 3))
               (fplus  (a $$ (fplus (evar i) sk_one, _ci 2))
                  (fplus (a $$ (fplus (evar i) sk_one, _ci 1))
                     (a $$ (fplus (evar i) sk_one, _ci 0))))));
       c.vid,
       SymbLinear[
         0, fplus (fplus (c $ sk_zero)
                     (a $$ (evar i, sk_zero)))
                   (a $$ (iplus1, sk_zero));
         1, fplus
           (fplus (c $ sk_one)
              (fplus (a $$ (evar i, sk_one))
                  (a $$ (evar i, sk_zero))))
           (fplus (a $$ (iplus1, sk_one))
              (a $$ (iplus1, sk_zero)))]];
  in
  ()


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
  test_03bis ();
  test_03ter ();
  test_04 ();
  file_defined_tests ()
