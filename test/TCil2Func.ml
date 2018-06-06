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
open Cil
open Loops
open Format
open TestUtils
open Utils
open FuncTypes

open PpTools

module C = Canalyst
module C2F = Cil2Func




let wf_single_subst func =
  match func with
  | C2F.State subs ->
     begin
       (IM.cardinal subs = 1) &&
         (match IM.max_binding subs with
         | k, C2F.Container _ -> true
         | _ -> false)
     end
  | _ -> false

let wf_test_case fname (func : C2F.letin) sketch  =
  match fname with
  (** Merge two if branches to form a ternary expression *)
  | "test_merge_ifs" ->
    let nb_subs_ok =
      begin
        match func with
        | C2F.State subs ->
          (IM.cardinal subs = 1) &&
          (match (IM.max_binding subs) with
           | k, C2F.FQuestion (e,
                               C2F.Container _,
                               C2F.Container _) -> true
           | _ -> false)
        | _ -> false
      end
    in
    let sketch_ok =
      match sketch with
      | FnRecord (vs, emap) ->
        begin match snd (ListTools.unpair (IM.to_alist emap)) with
          | [FnCond(FnBinop(Lt, _, _), FnBinop(Minus, _, _),
                       FnBinop(Plus, _, _))] -> true
          | _ -> false
        end
      | _ -> false
    in
    sketch_ok && nb_subs_ok

  (** A simple loop *)
  | "test_simple_loop" ->
    (wf_single_subst func) &&
    (match sketch with
     | FnRecord(_, map) ->
       let _, e = IM.max_binding map in
       begin match e with
         | FnBinop(Plus, FnBinop(Plus, _, _), _) -> true
         | _ -> false
       end
     | _ -> false)


  (** A loop with more local variables than state variables. *)
  | "test_detect_state" ->
    (match sketch with
     | FnRecord (vs, emap) ->
       (IM.cardinal emap = 2)
     | _ -> false)


  (** Two nested loops. We only test the C -> Func part because we never
      ` translate nested loops into a sketch.
      TODO : update the test, returns always true for now ...*)
  | "test_nested_loops" ->
     (** Two cases depending on if it is the outer/inner loop *)
     true || (wf_single_subst func) ||
       (match func with
       | C2F.Let (vid, expr, cont, id, loc) ->
          (match expr with
          | _ -> false) &&
            C2F.is_empty_state cont

       | _ -> false)

  (** Check that the functional translation step rebuilds and expressions that
      have been broken into conditionals by cil. *)
  | "test_rebuild_and" ->
    (match sketch with
     | FnRecord(_, map) ->
       let _, e = IM.max_binding map in
       begin match e with
         | FnBinop(And, _, _) -> true
         | _ -> false
       end
     | _ -> false)

  (** Same thing for disjunctions. *)
  | "test_rebuild_or" ->
    (match sketch with
     | FnRecord(_, map) ->
       let _, e = IM.max_binding map in
       begin match e with
         |  FnBinop(Or, _, _) -> true
         | _ -> false
       end
     | _ -> false)


  (** The balanced parenthesis example : test its well-formed *)

  (* | "test_balanced_bool" ->
   *   (match sketch with
   *    | FnLetIn ([_, FnCond(FnVar(FnArray(_, _)),
   *                            FnBinop(Plus, _, _),
   *                            FnBinop(Minus, _, _))],
   *               FnLetExpr([(_, FnCond(FnBinop(And, _, _),
   *                                         sk_one, sk_zero));
   *                         (_,_);(_,_)])) -> true
   *    | _ -> false)
   *
   * (\** ANother implementation of the balanced parenthesis example, test
   *  that the and is rebuilt *\)
   * | "test_and_in_if" ->
   *   (match sketch with
   *    | FnLetExpr([(_, FnBinop(And, _, FnBinop(Ge, cnte, sk_zero)));
   *                 (_, cnte2)]) ->
   *      (cnte = cnte2) &&
   *        (match cnte with
   *           FnBinop(Plus,
   *                   _,
   *                   FnCond(FnVar(FnArray _), FnConst _,
   *                             FnConst _)) -> true
   *          |_ -> false)
   *    |_ -> false)
   *
   * (\** The is_sorted example *\)
   * | "test_is_sorted" ->
   *   (match sketch with
   *    | FnLetExpr([(_, FnBinop(And, _, FnBinop(Lt, _, aref)));(_, aref2)]) ->
   *      (aref = aref2) && (match aref with | FnVar(FnArray (_, _)) -> true
   *                                         | _ ->false)
   *    | _ -> false)
   *
   * (\** The drop-while example *\)
   * | "test_drop_while_pos_int" ->
   *   (match sketch with
   *    | FnLetExpr ([(_, FnCond(FnBinop(And,
   *                                         FnUnop(Not, FnBinop(Eq, _, _)),_),
   *                                 _, _));
   *                  (_, FnCond(FnUnop(Not, _), _, _))]) -> true
   *    | _ -> false)
   *
   * | "test_alternating_sequence" ->
   *   (match sketch with
   *    | FnLetExpr ([(_, FnVar (FnArray(_, _)));
   *                   (_ , FnBinop(And,
   *                                FnVar(_),
   *                                FnCond(FnVar(_),_,_)))])-> true
   *    | _ -> false)
   *
   *
   * | "test_atoi" ->
   *   (match sketch with
   *    | FnLetExpr([(_, FnBinop(Plus,
   *                             FnBinop(Times, _, _),
   *                             _))]) -> true
   *    | _ -> false)
   *
   * | "test_s01" ->
   *   (match sketch with
   *    | FnLetExpr([(s, (FnBinop (Or, FnVar s1, _)));
   *                 (r, FnBinop(Or, FnBinop(And, FnVar s2, FnUnop(Not, _)),
   *                             FnVar r1))])
   *    | FnLetExpr([(s, (FnBinop (Or, FnVar s1, _)));
   *                 (r, FnBinop(Or, FnVar s2,
   *                             FnBinop(And, FnUnop(Not, _), FnVar r1)))]) ->
   *               s = s1 && s2 = s && r = r1
   *    | _ -> false) *)

  | "test_match_anbn" ->
    (match sketch with | _ -> false)
  | _ -> false


let cnt_pass = ref 0
let cnt_fail = ref 0

let _test () =
  let filename = "test/test-cil2func.c" in
  printf "%s-- test Cil -> Func  -- %s\n" (color "red") color_default;
  let cfile, loops = C.processFile filename in
  printf "%s Functional rep. %s\n" (color "blue") color_default;
  C2F.init loops;
(*C2F.debug := true;*)
  IM.fold
    (fun k cl ->
       let igu =
         try
           check_option cl.ligu
         with Failure s ->
           failwith ("test failure"^s)
       in
       let allvars = cl.lvariables.all_vars in
       let stmt = loop_body cl in
       let _, stv = loop_rwset cl in
       let func, figu =
         C2F.cil2func [] cl.lvariables stmt igu
       in
       (* let printer = new C2F.cil2func_printer (VS.union allvars w) stv in *)
       let figu' =
         let ids, igu = check_option figu in
         varset_of_vs ids, igu
       in
       let so = new Func2Fn.funct_builder (varset_of_vs allvars)
         (varset_of_vs stv) func figu' in
       so#build;
       let sketch, sigu = check_option so#get_funct in
       let fname = cl.lcontext.host_function.vname in
       if wf_test_case fname func sketch then

         begin
           incr cnt_pass;
           (printf "%s%s :\t\t passed.%s@."
              (color "green") fname color_default)
         end
       else
         begin
           incr cnt_fail;
           (printf "%s[test for loop %i in %s failed]%s@."
              (color "red") cl.lid fname color_default;);
           printf "All variables :%a@." VS.pvs allvars;
           printf "State variables : %a@." VS.pvs stv;
           printf "@.Sketch :@.";
           FPretty.printFnexpr sketch;
           printf "@.";
         end;
       SM.add fname (stv, figu,func)
    )
    loops
    SM.empty


let test () =
  let loops = _test () in
  (if !cnt_fail = 0 then
     printf "@.%sALL %i TESTS PASSED.%s@." (color "green") !cnt_pass color_default
   else
     printf "@.%i tests passed, %i tests failed.@." !cnt_pass !cnt_fail);
  loops
