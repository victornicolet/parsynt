open Cil
open Utils
open Loops
open Printf
open Prefunc

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

let rec do_il hm g il =
  List.iter (fun i -> do_i hm g i) il

and do_i hm g (ins : Cil.instr) =
 match ins with
 | Set (lv, exp, _) ->
    let vset = VS.elements (Utils.sovv ~onlyNoOffset:true lv) in
    if List.length vset = 1
    then
      begin
        let v = List.hd vset in
        let fexp = build g exp v in
        let olde =
          try
            IH.find hm v.vid
          with Not_found -> Container (v2e v) in
        let nexp = replace v.vid olde fexp in
        if !debug then
          Printf.printf "Replacing %s\n by %s\n"
            (string_of_prefunc olde) (string_of_prefunc nexp);
        IH.replace hm v.vid nexp
      end
    else ()
 | _ -> ()

and do_b hm g b =
  List.iter (fun s -> do_s hm g s) b.bstmts

and do_s hm g stm =
  match stm.skind with
    Instr il ->
      do_il hm g il
  | If (e, b1, b2, _) ->
     ppe e;
     let cond1 = gcompose g (GCond (e, GEmpty)) in
     do_b hm cond1 b1;
     ppe (neg_exp e);
     if non_empty_block b2 then 
       let cond2 = gcompose g (GCond ((neg_exp e), GEmpty)) in
       do_b hm cond2 b2;
  | Loop (b, _ ,_, _) ->
     begin
       try
         let igu = (IH.find !loops stm.sid).Cloop.loopIGU in
         let forlp = gcompose g (GFor (checkOption igu, GEmpty)) in
         do_b hm forlp b
       with
         Not_found -> raise (Failure "Found a loop statement not in \
 the program loops.")
     end
  | Block b -> do_b hm g b
  | _ -> ()


let prefunc stmtlist statevars =
  if !debug then print_endline "---Transform to SSA---";
  let assignments = IH.create 10 in
  List.iter (fun s -> do_s assignments GEmpty s) stmtlist;
  if !debug then
    begin
      IH.iter (fun i v -> printf "%i = %s\n" i (string_of_prefunc v))
        assignments;
      printf "-----------\n"
    end;
  assignments

(** ------------------------------------------------------------------*)
(**
    Control-flow graph operations to remove the statements updating
    the loop index and the break statement.
    Another solution would be to patch Cil so it keeps the structure of the
    for loops and doesn't translate them to this while(1) structure.
*)

let removeFromCFG (stm : Cil.stmt) =
  let succs = stm.succs in
  let preds = stm.preds in
  let eq_stm s = (stm.sid = s.sid) in
  List.iter (fun s -> (s.succs <- List.filter eq_stm s.succs)) preds;
  List.iter (fun s -> (s.preds <- List.filter eq_stm s.preds)) succs

let removeIGU (whileStmt : Cil.stmt) ((i, g, u) : forIGU) =
  match whileStmt.skind with
  | Loop (blk, loc, so1, so2) ->
	let stmts0 = blk.bstmts in
    (** Remove the instruction incrementing the index *)
	let rec auxi ilist inst =
	  if inst = u then
        begin
          (if !debug then (print_endline "Removing:"; ppi inst) else ());
          ilist
        end
      else inst::ilist in
    (** Remove the statement containing the break *)
	let rec auxs stmlist stm =
	  match stm.skind with
	  | If (e, b1, b2, _) when e = g ->
         begin
           if !debug then
             (print_string "Removing If stmt with expression ";
              ppe e;);
           removeFromCFG stm;
           stmlist
         end
	  | Instr ilist0 ->
		let ilist = List.fold_left auxi [] ilist0 in
		stm.skind <- (Instr ilist);
		stmlist@[stm]
	  | _ -> stmlist@[stm]
	in
	let stmts = List.fold_left auxs [] stmts0 in
	blk.bstmts <- stmts
  | _ -> raise (Failure "Expected a loop statement in removeIGU")

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
      mutable state : int list;
      mutable parentLoops : int list;
      mutable definedInVars: defsMap;
      mutable usedOutVars: varinfo list;
      mutable allVars: VS.t ;
    }

    let fromCloop (sid: int) (cl : Cloop.t) =
      if !debug then Printf.printf "--- Loop %i --> SSA ---\n" sid;
      let stateVars = Utils.outer_join_lists
	    (match cl.Cloop.rwset with (r, w, rw) -> w, rw) in
  (**  let loopIndex = indexOfIGU  (checkOption cl.Cloop.loopIGU) in *)
      let loop_stmt = cl.Cloop.loopStatement in
      let loop_igu = checkOption cl.Cloop.loopIGU in
      removeIGU loop_stmt loop_igu;
      if !debug then
        begin
          Printf.printf "Loop after removing IGU:\n";
          pps cl.Cloop.loopStatement;
        end;
      let body_stmts =

        match loop_stmt.skind with
        | Loop (blk, _, _, _) -> blk.bstmts
        | _ -> raise (Failure "processLoop : this should be a loop statement.")
      in
      {
        sid = sid;
        igu = loop_igu;
        body = prefunc body_stmts stateVars;
        state = stateVars;
        parentLoops = cl.Cloop.parentLoops;
        definedInVars = cl.Cloop.definedInVars;
        usedOutVars = cl.Cloop.usedOutVars;
        allVars = VS.empty;
      }
end

(** Main entry point *)
let floops = IH.create 10

let processFile_l2s lps =
  loops := lps;
  begin
    IH.iter (fun sid cloop ->
      if (not cloop.Cloop.hasBreaks)
      then ()
      else
        begin
          let floop = Floop.fromCloop sid cloop in
          IH.add floops sid floop
        end)
      lps
  end;
  floops

let clear () =
  IH.clear !loops ;
  IH.clear floops;
