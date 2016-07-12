open Cil
open Format
open PpHelper
open Loops.Cloop
open Utils

module C = Canalyst
module C2F = Cil2Func
module LF = Loops2ssa.Floop

let wf_single_subst func =
  match func with
  | C2F.State (vs, subs) ->
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
       | C2F.State (vs, subs) ->
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
       | C2F.Let (vid, expr, cont, loc) ->
          (match expr with
          | C2F.FRec (_, _) -> true
          | _ -> false) &&
            C2F.is_empty_state cont

       | _ -> false
       )

  | _ -> false


let test () =
  let filename = "test/test-cil2func.c" in
  printf "-- test Cil -> Func  -- \n";
  ignore(C.processFile filename);
  printf "%s Functional rep. %s\n" (color "blue") default;
  let loops = C.getLoops () in
  C2F.init loops;
  IH.iter
    (fun k cl ->
      let stmt = mkBlock(cl.statements) in
      let stateVars = ListTools.outer_join_lists
	    (match cl.rwset with (r, w, rw) -> w, rw) in
      let vars = VSOps.vs_of_defsMap cl.definedInVars in
      let stv = VSOps.subset_of_list stateVars vars in
      let func = C2F.cil2func stmt stv in
      let fname = cl.parentFunction.vname in
      if wf_test_case fname func then
        (printf "%s%s :\t passed.%s@."
           (color "green") fname default)
      else
        (printf "%s[test for loop %i in %s failed]%s@."
           (color "red") cl.sid fname default;);
      C2F.printlet func;
      printf "@.";
    )
    loops;;
