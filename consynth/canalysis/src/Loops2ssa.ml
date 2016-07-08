open Cil
open Utils
open Loops
open Printf
open Prefunc
open LoopsHelper
open ListTools

module IH = Inthash
module VS = Utils.VS

let debug = ref false
(** The loops in the files *)
let loops = ref (IH.create 10)

(**
    First simple solution for converting to a SSA form : for each statement
    in the loop, find the reaching defintions and inline them in the
    assignement. The result will be a one-assignement per state variable
    loop body.
*)

let rec do_il vs hm g il =
  List.iter (fun i -> do_i vs hm g i) il


(** Instruction *)
and do_i vs hm g (ins : Cil.instr) =
 match ins with
 | Set (lv, exp, _) ->
    let vset = VSOps.sovv ~onlyNoOffset:true lv in
    (**
        Only one non-offset variable should appear on the
        left-hand side of an assignment.
    *)
    if VS.cardinal vset = 1
    then
      begin
        let v = VS.min_elt vset in
        let nvs = if VS.mem v vs then
            vs
          else
            begin
              if !debug then
                eprintf "Warning : adding new state variables.";
              VS.add v vs
            end
        in
        let fnexp = build g exp v  (VSOps.vids_of_vs vs) in
        (** If any other state variable is used in the expression,
        replace it by its current function *)
        let used_in_f = VS.diff (VS.inter (vs_of_fexp nvs fnexp) nvs) vset in
        let new_lam =
          VS.fold
            (fun vi lam ->
              try
                let pf = IH.find hm vi.vid in
                Let (vi.vid, (reduce pf), lam)
              with Not_found ->
                lam
            )
            used_in_f
            (Exp fnexp) in
        (**
            Find the old function for the variable in the current
            variable->function mapping.
        *)
        let olde =
          try
            IH.find hm v.vid
          with Not_found ->  Empty v in
        (**
           And append to the let .. in let .. sequence the new expression
        *)
        let nexp = let_in_func v olde new_lam in
        if !debug then
          Printf.printf "Replacing %s\n by %s\n"
            (string_of_prefunc olde) (string_of_prefunc nexp);
        IH.replace hm v.vid nexp
      end
    else ()
 | Call (lvo, ef, el, _) ->
    begin
      match lvo with
        (**
            This is not an assignment, we do not take in account
            side effects for now.
        *)
      | None -> ()
      | Some lv ->
         begin
           match ef with
           | Lval (Var vi, _) ->
              begin
                () (** TODO *)
              end
           | _ ->  ()
         end
    end
 | _ -> ()


(** Block -> list of statements *)
and do_b vs index_map functions_map g b =
  List.iter (fun s -> do_s vs index_map functions_map g s) b.bstmts

(** Statements *)
and do_s vs ix hm g stm =
  match stm.skind with
    Instr il ->
      do_il vs hm g il
  | If (e, b1, b2, _) ->
     let cond1 = gcompose g (GCond (e, GEmpty)) in
     do_b vs ix hm cond1 b1;
     if !debug then
       begin
         printf "Negation of ";
         ppe e;
         printf " is ";
         ppe (neg_exp e);
         print_endline ".";
       end;
     if non_empty_block b2 then
       let cond2 = gcompose g (GCond ((neg_exp e), GEmpty)) in
       do_b vs ix hm cond2 b2;
  | Loop (b, _ ,_, _) ->
     begin
       try
         let igu = checkOption ((IH.find !loops stm.sid).Cloop.loopIGU) in
         let forlp = gcompose g (GFor (igu, GEmpty)) in
         let nestd_lp_ix = VS.max_elt (Loops.indexOfIGU igu) in
         IH.add ix nestd_lp_ix.vid nestd_lp_ix;
         do_b vs ix hm forlp b
       with
         Not_found -> raise (Failure "Found a loop statement not in \
 the program loops.")
     end
  | Block b -> do_b vs ix hm g b
  | _ -> ()


let prefunc stmtlist statevs loop_index =
  if !debug then print_endline "---Transform to SSA---";
  let assignments = IH.create 10 in
  let idx = IH.create 5 in
  IH.add idx loop_index.vid loop_index;
  List.iter (fun s -> do_s statevs idx assignments GEmpty s)
    stmtlist;
  if !debug then
    begin
      IH.iter (fun i v -> printf "%i = %s\n" i (string_of_prefunc v))
        assignments;
      printf "-----------\n"
    end;
  (**
     Check that state-variables set and assignments are coherent,
     if not add the necessary state variables.
  *)
  let all_indexes = VSOps.vs_of_inthash idx in
  let enriched_state_vars =
    IH.fold
      (fun i pF sv ->
        match pF with
        | Empty vi -> sv
        | Func (vi, l) ->
           if VS.mem vi sv
           then sv
           else VS.add vi sv)
      assignments
      statevs
  in
  assignments, enriched_state_vars,  all_indexes

(** ------------------------------------------------------------------*)
(**
    main interface functions. From the result of using the Loops module to
    compute some information, deduce a semi-functional representation
    of the loop body.
*)


module Floop = struct
    type t = {
      sid: int;
      mutable igu: forIGU;
      mutable body : preFunc IH.t;
      mutable parentLoops : int list;
      mutable state : int list;
      mutable indexes : int list;
      mutable usedOutVars: Cil.varinfo list;
      mutable allVars: VS.t ;
    }

    let fromCloop (sid: int) (cl : Cloop.t) =
      if !debug then Printf.printf "--- Loop %i --> SSA ---\n" sid;
      let stateVars = outer_join_lists
	    (match cl.Cloop.rwset with (r, w, rw) -> w, rw) in
      let vars = VSOps.vs_of_defsMap cl.Cloop.definedInVars in
      let stateSet = VSOps.subset_of_list stateVars vars in
      let loop_igu = checkOption cl.Cloop.loopIGU in
      if !debug then
        begin
          Printf.printf "Loop after removing IGU:\n";
          pps cl.Cloop.loopStatement;
        end;
      let body_stmts = cl.Cloop.statements in
      let index = Loops.indexOfIGU loop_igu in
      let func_body, statevs, indexes =
        prefunc body_stmts stateSet (VS.max_elt index)
      in
      let allvs = VS.union vars statevs in
      {
        sid = sid;
        igu = loop_igu;
        body = func_body;
        state = VSOps.vids_of_vs statevs;
        indexes = VSOps.vids_of_vs indexes;
        parentLoops = cl.Cloop.parentLoops;
        usedOutVars = cl.Cloop.usedOutVars;
        allVars = allvs;
      }
end

(** Main entry point *)
let floops = IH.create 10

let processFile_l2s lps =
  loops := lps;
  begin
    IH.iter (fun sid cloop ->
      let floop = Floop.fromCloop sid cloop in
      IH.add floops sid floop)
      lps
  end;
  floops

let clear () =
  IH.clear !loops ;
  IH.clear floops;
