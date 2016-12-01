open Cil
open Findloops.Cloop
open Format
open PpHelper
open TestUtils
open Utils


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

let wf_test_case fname (func : C2F.letin) =
  match fname with
  | "test_merge_ifs" ->
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
  | "test_simple_loop" -> wf_single_subst func

  | "test_nested_loops" ->
     (** Two cases depending on if it is the outer/inner loop *)
     (wf_single_subst func) ||
       (match func with
       | C2F.Let (vid, expr, cont, id, loc) ->
          (match expr with
          | C2F.FRec (_, _) -> true
          | _ -> false) &&
            C2F.is_empty_state cont

       | _ -> false
       )
  | "test_balanced_bool" ->
    false

  | _ -> false


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
       CilTools.ppbk stmt;
       let func, figu = C2F.cil2func  (VS.union allvars w) stv stmt igu in
       let printer = new C2F.cil2func_printer (VS.union allvars w) stv in
       let so = new Sketch.Body.sketch_builder allvars
         stv func figu in
       so#build;
       let sketch, sigu = check_option so#get_sketch in
       let fname = cl.host_function.vname in
       if wf_test_case fname func then
         (printf "%s%s :\t passed.%s@."
            (color "green") fname default)
       else
         begin
         (printf "%s[test for loop %i in %s failed]%s@."
            (color "red") cl.sid fname default;);
         printf "All variables :%a@." VSOps.pvs (VS.union allvars w);
         printf "State variables : %a@." VSOps.pvs stv
         end;
       printer#printlet func;
       printf "@.Sketch :@.";
       SPretty.printSklet sketch;
       printf "@.";
       SM.add fname (stv, figu,func)
    )
    loops
    SM.empty
;;

test ();
