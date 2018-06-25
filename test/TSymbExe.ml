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
open Fn
open FnPretty
open SymbExe
open Utils
open TestUtils
open ExpressionReduction
open VariableDiscovery
open Format

let verbose = ref false

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
        intermediate_states = IM.empty;
        inputs = ES.empty;
      }
    | Some xinfo -> xinfo
  in
  let xinfo' = unfold_once ~silent:false xinfo funct in
  begin
    try
      List.iter
        (fun (vid, stv_type) ->
           let e = IM.find vid xinfo'.state_exprs in
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
            pp_typ (type_of e) cp_fnexpr e ) xinfo'.state_exprs;
      msg_failed (tname^" : "^s)
  end;
  xinfo'

let test_01 () =
  let vars = vardefs "((sum int) (i int) (c int_array) (A int_array))" in
  let cont = make_context vars "((sum c) (i) (A) (sum c i A) (sum c))" in
  let c = vars#get "c" in
  let sum = vars#get "sum" in
  let funct =
    _letin
      [(FnArray (FnVariable c, sk_zero), sk_zero);
       (FnVariable sum, sk_zero)]
      (_letin
         [(FnArray (FnVariable c, sk_one)), (FnVar (FnArray (FnVariable c, sk_zero)))]
         (FnRecord(cont.state_vars, identity_map cont.state_vars)))
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
  let inloop_type = record_type inloop_state in
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
                      (inloop_state, FnRecord(inloop_state, IM.of_alist [c.vid, evar c])),
                      (* Body of the loop *)
                      (state_binder,
                       (_letin [_self state_binder c]
                          (_letin [(FnArray (var c, _ci 2)), _ci 2]
                             (_let [var c, evar c]))))))]
            (evar tup)))
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
  let instt = record_type inst in
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
                        (inst, FnRecord(inst, IM.of_alist [c.vid, evar c])),
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
      r1 with
      index_exprs = increment_all_indexes (create_symbol_map cont.index_vars);
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
  let instt = record_type inst in
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
             (inst, FnRecord(inst, IM.of_alist [sum.vid, evar sum])),
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
  let instt = record_type inst in
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
             (inst, FnRecord(inst, IM.of_alist [sum.vid, evar sum])),
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
      r1 with
      index_exprs = increment_all_indexes (create_symbol_map cont.index_vars);
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
      r2 with
      index_exprs =
        increment_all_indexes
          (increment_all_indexes
             (create_symbol_map cont.index_vars));
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
  let intype = record_type inctx.state_vars in
  let tup = mkFnVar "tup" intype in
  let bnds = mkFnVar "bound" intype in
  let func =
    (_letin [FnVariable tup,
             FnRec((sk_zero, (flt (evar i) (_ci 5)), (fplus (evar j) sk_one)),
                   (inctx.state_vars, FnRecord(inctx.state_vars,
                                               IM.of_alist [sum.vid, sk_zero; mtr.vid, sk_zero;c.vid, evar c])),
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
            r1 with
            index_exprs = increment_all_indexes (create_symbol_map cont.index_vars);
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


let test_05 () =
  let vars = vardefs "((mtr int) (c int_array) (mtrr int) (a int_int_array) (i int) (j int))" in
  let cont = make_context vars "((mtr mtrr c) (i) (a) (mtr mtrr c i j a) (mtr mtrr c))" in
  let c = vars#get "c" in
  let mtr = vars#get "mtr" in
  let mtrr = vars#get "mtrr" in
  let a = vars#get "a" in
  let j = vars#get "j" in let i = vars#get "i" in
  let inctx = make_context vars "((mtr c) (j) (a) (mtr mtrr c j a) (mtr c))" in
  let intype = record_type inctx.state_vars in
  let tup = mkFnVar "tup" intype in
  let bnds = mkFnVar "bound" intype in
  let func =
    (_letin [FnVariable tup,
             FnRec((sk_zero, (flt (evar i) (_ci 5)), (fplus (evar j) sk_one)),
                   (inctx.state_vars, FnRecord(inctx.state_vars,
                                               IM.of_alist [mtr.vid, sk_zero;c.vid, evar c])),
                   (bnds,
                    (_letin [ _self bnds mtr; _self bnds c]
                       (_letin [var c, FnArraySet(evar c, evar j, (fplus (c $ (evar j))
                                                                     (a $$ (evar i, evar j))))]
                          (_let [var c, evar c;
                                 var mtr, fmax (fplus (c $ (evar j)) (evar mtr)) sk_zero])))))]
       (_let [_self tup c;
              _self tup mtr;
              var mtrr, fmax (evar mtrr) (_inrec tup mtr)]))
  in
  let mtrr1 =
      fmax (evar mtrr)
        (fmax
           (fplus (fplus (c $ (_ci 4)) (a $$ (evar i, _ci 4)))
              (fmax
                 (fplus (fplus (c $ (_ci 3)) (a $$ (evar i, _ci 3)))
                    (fmax
                       (fplus (fplus (c $ (_ci 2)) (a $$ (evar i, _ci 2)))
                          (fmax
                             (fplus (fplus (c $ (_ci 1)) (a $$ (evar i, _ci 1)))
                                (fmax
                                   (fplus (c $ (_ci 0)) (a $$ (evar i, _ci 0)))
                                   (_ci 0)))
                             (_ci 0)))
                       (_ci 0)))
                 (_ci 0)))
           (_ci 0))
  in
  let r1 =
    symbolic_execution_test "mtrr" vars cont func 2
      [c.vid, SymbLinear [
         0, (fplus (c $ (_ci 0))
               (a $$ (evar i, _ci 0)));
         1, (fplus (c $ (_ci 1))
               (a $$ (evar i, _ci 1)));
         2, (fplus (c $ (_ci 2))
               (a $$ (evar i, _ci 2)));
         3, (fplus (c $ (_ci 3))
               (a $$ (evar i, _ci 3)));];
       mtrr.vid, SymbScalar mtrr1
      ]
  in
  let ip1 = fplus (evar i) sk_one in
  let mtr2 =
    (fmax
       (fplus
          (fplus (fplus (c $ (_ci 4)) (a $$ (evar i, _ci 4))) (a $$ (ip1, _ci 4)))
          (fmax
             (fplus
                (fplus (fplus (c $ (_ci 3)) (a $$ (evar i, _ci 3))) (a $$ (ip1, _ci 3)))
                (fmax
                   (fplus
                      (fplus (fplus (c $ (_ci 2)) (a $$ (evar i, _ci 2))) (a $$ (ip1, _ci 2)))
                      (fmax
                         (fplus
                            (fplus (fplus (c $ (_ci 1)) (a $$ (evar i, _ci 1))) (a $$ (ip1, _ci 1)))
                            (fmax
                               (fplus (fplus (c $ (_ci 0)) (a $$ (evar i, _ci 0)))  (a $$ (ip1, _ci 0)))
                               (_ci 0)))
                         (_ci 0)))
                   (_ci 0)))
             (_ci 0)))
       (_ci 0))
  in
  let _ =
    symbolic_execution_test
      ~_xinfo:
        (Some {
            r1 with
            index_exprs = increment_all_indexes (create_symbol_map cont.index_vars);
          })
      "mtrr, second unfolding" vars cont func 2
      [
        c.vid, SymbLinear [
          0, (fplus
                (fplus (c $ (_ci 0))
                   (a $$ (evar i, _ci 0)))
                (a $$ (ip1, _ci 0)));
          1, (fplus
                (fplus (c $ (_ci 1))
                   (a $$ (evar i, _ci 1)))
                (a $$ (ip1, _ci 1)));
          2,(fplus
               (fplus (c $ (_ci 2))
                  (a $$ (evar i, _ci 2)))
               (a $$ (ip1, _ci 2)));
          3, (fplus
                (fplus (c $ (_ci 3))
                   (a $$ (evar i, _ci 3)))
                (a $$ (ip1, _ci 3)))];
       mtrr.vid, SymbScalar (fmax mtrr1 mtr2)
      ]
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
  test_05 ();
  file_defined_tests ()
