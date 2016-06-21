open Cil
open Utils
open Loops

module IH = Inthash

let debug = ref true

let removeFromCFG (stm : Cil.stmt) =
  let succs = stm.succs in
  let preds = stm.preds in
  let eq_stm s = (stm.sid = s.sid) in
  List.iter (fun s -> (s.succs <- List.filter eq_stm s.succs)) preds;
  List.iter (fun s -> (s.preds <- List.filter eq_stm s.preds)) succs
(**
   We cannot convert the Cil body of the loop directly, we want to remove the
   effect on the loop index.
*)
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
    (** Remvoe the statement containing the break *)
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

let processLoop (sid : int) (cl : Cloop.t) =
  let stateVars = Utils.outer_join_lists
	(match cl.Cloop.rwset with (r, w, rw) -> w, rw) in
  let loopIndex = indexOfIGU  (checkOption cl.Cloop.loopIGU) in
  removeIGU cl.Cloop.loopStatement (checkOption cl.Cloop.loopIGU);
  if !debug then pps cl.Cloop.loopStatement;
  ()


(** Main entry point *)
let processFile_l2s cfile =
  ignore(Loops.processFile cfile);
  let loops = Loops.processedLoops () in
  IH.iter processLoop loops;
  loops
