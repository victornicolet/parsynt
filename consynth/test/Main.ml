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
module TDis = TDiscovery

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

let counting_blocks () =
  let n_vi, n, n_e =
    let vi = make_int_varinfo "N" in
    (vi, T.mkVar vi, T.mkVarExpr vi)
  in

  (** Index var *)
  let i_vi, i, i_e =
    let vi = make_int_varinfo "ind" in
    (vi, T.mkVar vi, T.mkVarExpr vi)
  in

  let i_set, i_map = VS.singleton i_vi, IM.singleton i_vi.vid i_e
  in

  let sigu = i_set, (T.SkLetExpr [(i, (T.SkConst (T.CInt 0)))],
                     T.SkBinop (T.Lt, i_e, n_e),
                     T.SkLetExpr [(i, T.SkBinop (T.Plus, i_e, sk_one))])
  in
  (** Input arrray *)
  let a_vi, a, a_e =
    let vi = make_int_varinfo "array" in
    (vi, T.mkVar ~offsets:[i_e] vi, T.mkVarExpr ~offsets:[i_e] vi)
  in

  (** State variables : a flag and a counter *)

  let f_vi, f, f_e =
    let vi = make_bool_varinfo "flag" in
    (vi, T.mkVar vi, T.mkVarExpr vi)
  in

  let count_vi, count, count_e =
    let vi = make_int_varinfo "count" in
    (vi, T.mkVar vi, T.mkVarExpr vi)
  in
  let state = VS.of_list [f_vi; count_vi] in
  let all_vars = VS.union (VS.add a_vi state) i_set in
  (** Function *)
  let counting_block =
    T.SkLetExpr [(f, a_e);
                 (count,
                  T.SkBinop(T.Plus,
                            count_e,
                            T.SkQuestion(
                              T.SkBinop(T.And, T.SkUnop(T.Not, f_e), a_e),
                              sk_one,
                              sk_zero)))]
  in
  let new_state, new_func =
    VariableDiscovery.discover state counting_block sigu
  in
  let new_func = SketchBody.optims new_func in
  fprintf std_formatter
    "New state is : %a@. New function is : @.%a"
    VSOps.pvs new_state SPretty.pp_sklet new_func;
  IH.copy_into VariableDiscovery.discovered_aux Sketch.Join.auxiliary_variables;
  let join = Sketch.Join.build new_state new_func in
  Local.dump_sketch := true;
  let res =  Local.compile_and_fetch Canalyst.pp_sketch
      { ro_vars_ids = [a_vi.Cil.vid; i_vi.Cil.vid];
        state_vars_ids = VSOps.vids_of_vs new_state;
        var_set = VS.union new_state all_vars ;
        loop_body = new_func; join_body = join;
        sketch_igu = sigu;
        reaching_consts = IM.empty;
      }
  in ();;



counting_blocks ();
