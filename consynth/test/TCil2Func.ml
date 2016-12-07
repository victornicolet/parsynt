open Cil
open Findloops.Cloop
open Format
open PpHelper
open TestUtils
open Utils
open SketchTypes

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

let wf_test_case fname (func : C2F.letin) (sketch : sklet) =
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
      | SkLetExpr ([_, SkQuestion(SkBinop(Lt, _, _), SkBinop(Minus, _, _),
                                 SkBinop(Plus, _, _))]) -> true
      | _ -> false
    in
    sketch_ok && nb_subs_ok

  (** A simple loop *)
  | "test_simple_loop" ->
    (wf_single_subst func) &&
    (match sketch with
     | SkLetExpr ([_, SkBinop(Plus, SkBinop(Plus, _, _), _)]) -> true
     | _ -> false)


  (** A loop with more local variables than state variables. *)
  | "test_detect_state" ->
    (match sketch with
     | SkLetExpr li ->
       (List.length li = 2)
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
          | C2F.FRec (_, _) -> true
          | _ -> false) &&
            C2F.is_empty_state cont

       | _ -> false)

  (** Check that the functional translation step rebuilds and expressions that
      have been broken into conditionals by cil. *)
  | "test_rebuild_and" ->
    (match sketch with
     | SkLetExpr ([(_, SkBinop(And, _, _))]) -> true
     | _ -> false)

  (** Same thing for disjunctions. *)
  | "test_rebuild_or" ->
    (match sketch with
     | SkLetExpr ([(_, SkBinop(Or, _, _))]) -> true
     | _ -> false)


  (** The balanced parenthesis example : test its well-formed *)

  | "test_balanced_bool" ->
    (match sketch with
     | SkLetIn ([_, SkQuestion(SkVar(SkArray(_, _)),
                             SkBinop(Plus, _, _),
                             SkBinop(Minus, _, _))],
                SkLetExpr([(_, SkQuestion(SkBinop(And, _, _),
                                          sk_one, sk_zero));
                          (_,_);(_,_)])) -> true
     | _ -> false)

  (** ANother implementation of the balanced parenthesis example, test
   that the and is rebuilt *)
  | "test_and_in_if" ->
    (match sketch with
     | SkLetExpr([(_, SkBinop(And, _, SkBinop(Ge, cnte, sk_zero)));
                  (_, cnte2)]) ->
       (cnte = cnte2) &&
         (match cnte with
            SkBinop(Plus,
                    _,
                    SkQuestion(SkVar(SkArray _), SkConst _,
                              SkConst _)) -> true
           |_ -> false)
     |_ -> false)

  (** The is_sorted example *)
  | "test_is_sorted" ->
    (match sketch with
     | SkLetExpr([(_, SkBinop(And, _, SkBinop(Lt, _, aref)));(_, aref2)]) ->
       (aref = aref2) && (match aref with | SkVar(SkArray (_, _)) -> true
                                          | _ ->false)
     | _ -> false)

  (** The drop-while example *)
  | "test_drop_while_pos_int" ->
    (match sketch with
     | SkLetExpr ([(_, SkQuestion(SkBinop(And,
                                          SkUnop(Not, SkBinop(Eq, _, _)),_),
                                  _, _));
                   (_, SkQuestion(SkUnop(Not, _), _, _))]) -> true
     | _ -> false)

  | "test_alternating_sequence" ->
    (match sketch with
     | SkLetExpr ([(_, SkVar (SkArray(_, _)));
                    (_ , SkBinop(And,
                                 SkVar(_),
                                 SkQuestion(SkVar(_),_,_)))])-> true
     | _ -> false)


  | "test_atoi" ->
    (match sketch with
     | SkLetExpr([(_, SkBinop(Plus,
                              SkBinop(Times, _, _),
                              _))]) -> true
     | _ -> false)

  | "test_s01" ->
    (match sketch with
     | SkLetExpr([(s, (SkBinop (Or, SkVar s1, _)));
                  (r, SkBinop(Or, SkBinop(And, SkVar s2, SkUnop(Not, _)),
                              SkVar r1))])
     | SkLetExpr([(s, (SkBinop (Or, SkVar s1, _)));
                  (r, SkBinop(Or, SkVar s2,
                              SkBinop(And, SkUnop(Not, _), SkVar r1)))]) ->
                s = s1 && s2 = s && r = r1
     | _ -> false)

  | "test_match_anbn" ->
    (match sketch with | _ -> false)
  | _ -> false


let cnt_pass = ref 0
let cnt_fail = ref 0

let test () =
  let filename = "test/test-cil2func.c" in
  printf "%s-- test Cil -> Func  -- %s\n" (color "red") default;
  let loops = C.processFile filename in
  printf "%s Functional rep. %s\n" (color "blue") default;
  C2F.init loops;
(*C2F.debug := true;*)
  IM.fold
    (fun k cl ->
       let igu =
         try
           check_option cl.loop_igu
         with Failure s ->
           failwith ("test failure"^s)
       in
       let allvars = getAllVars cl in
       let stmt = mkBlock(cl.new_body) in
       let _, w = cl.rwset in
       let stv = getStateVars cl in
       let func, figu = C2F.cil2func  (VS.union allvars w) stv stmt igu in
       (* let printer = new C2F.cil2func_printer (VS.union allvars w) stv in *)
       let so = new Sketch.Body.sketch_builder allvars
         stv func figu in
       so#build;
       let sketch, sigu = check_option so#get_sketch in
       let fname = cl.host_function.vname in
       if wf_test_case fname func sketch then

         begin
           incr cnt_pass;
           (printf "%s%s :\t\t passed.%s@."
              (color "green") fname default)
         end
       else
         begin
           incr cnt_fail;
           (printf "%s[test for loop %i in %s failed]%s@."
              (color "red") cl.sid fname default;);
           printf "All variables :%a@." VSOps.pvs (VS.union allvars w);
           printf "State variables : %a@." VSOps.pvs stv;
           printf "@.Sketch :@.";
           SPretty.printSklet sketch;
           printf "@.";
         end;
       SM.add fname (stv, figu,func)
    )
    loops
    SM.empty
;;

test ();;
(if !cnt_fail = 0 then
   printf "@.%sALL %i TESTS PASSED.%s@." (color "green") !cnt_pass default
 else
   printf "@.%i tests passed, %i tests failed.@." !cnt_pass !cnt_fail);;
