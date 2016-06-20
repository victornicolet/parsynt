open Cil
open Utils
open Loops

module IH = Inthash


(**
   We cannot convert the Cil body of the loop directly, we want to remove the
   effect on the loop index.
*)
let removeIGU (whileStmt : Cil.stmt) ((i, g, u) : forIGU) =
  match whileStmt.skind with
  | Loop (blk, loc, so1, so2) ->
	let stmts0 = blk.bstmts in
	let rec auxi ilist inst =
	  if inst = u then ilist else inst::ilist in
	let rec auxs stmlist stm =
	  match stm.skind with
	  | If (e, b1, b2, _) when e = g -> stmlist
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
  removeIGU cl.Cloop.loopStatement (checkOption cl.Cloop.loopIGU)


(** Main entry point *)
let processFile_l2s cfile =
  ignore(Loops.processFile cfile);
  let loops = Loops.processedLoops () in
  IH.iter processLoop loops;
  loops
