open Cil
open Canalyst
open Format
open PpHelper
open Findloops
open Utils
open Getopt
open TestUtils

module C2F = Cil2Func

(** Different test modules *)
(* module TC2F = TCil2Func *)
(* module TF2S = TFunc2Sketch *)
(* module TGDef = TGenDefs *)
(*module TSbx = TSymbExe *)
(* module TScm = TestSchemeParsing *)
(* module TDis = TDiscovery *)
(* module TExpr = TExpressions *)

let options = [
  ( 'd', "dump",  (set Local.dump_sketch true), None);
  ( 'g', "debug", (set Local.debug true), None);
  ( 'v', "debug-var", (set VariableDiscovery.debug true), None)
]

(* let testProcessFile () = *)
(*   if Array.length Sys.argv < 2 then *)
(*     begin *)
(*       TGDef.test (); *)
(*       let loopsm = TC2F.test () in *)
(*       TF2S.test loopsm; *)
(*       eprintf "Usage : ./Main.native [test file name]\n\n"; *)
(*       exit 0 *)
(*     end; *)
(*   let filename = "test/"^(Array.get Sys.argv 1) in *)
(*   printf "-- test processing file -- \n"; *)
(*   let loops = Canalyst.processFile filename in *)
(*   printf "-- finished --\n"; *)
(*   printf "%s Functional rep. %s\n" (color "blue") default; *)
(*   IM.iter *)
(*     (fun k cl -> *)
(*        let stmt = mkBlock(cl.Cloop.new_body) in *)
(*        let igu = check_option cl.Cloop.loop_igu in *)
(*        let r, stv = cl.Cloop.rwset in *)
(*        let letn, _ = C2F.cil2func stv stmt igu in *)
(*        C2F.printlet (stv, letn)) *)
(*     loops;; *)

(* open TMssReductions *)
(* open TCil2Func *)

(** Testing Z3 *)
open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Arithmetic
open Z3.Boolean
open Z3.Params
open Z3.Symbol

let test (ctx : context) =
  let params = mk_params ctx in
  add_bool params (mk_string ctx "pull_cheap_ite") true;
  add_bool params (mk_string ctx "ite_extra_rules") true;
  let a = (Expr.mk_const ctx (Symbol.mk_string ctx "x")
             (Boolean.mk_sort ctx))
  in
  let b = (Expr.mk_const ctx (Symbol.mk_string ctx "y")
             (Boolean.mk_sort ctx))
  in
  let c1 = (Expr.mk_const ctx (Symbol.mk_string ctx "c1")
             (Boolean.mk_sort ctx))
  in
  let c2 =(Expr.mk_const ctx (Symbol.mk_string ctx "c2")
             (Boolean.mk_sort ctx))
  in
  let itee =
    mk_ite ctx c1 (mk_ite ctx c2 (mk_ite ctx c2 a b) b) (mk_ite ctx (mk_not ctx c1) b a)
  in
  print_endline (Expr.get_simplify_help ctx);
  printf "Initially : %s@." (Expr.to_string itee);
  let itee_simpl =
    Expr.simplify itee (Some params)
  in
  printf "Simplified : %s@." (Expr.to_string itee_simpl);;


test (mk_context []);;
