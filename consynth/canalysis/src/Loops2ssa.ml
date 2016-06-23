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

let rec do_il vs hm g il =
  List.iter (fun i -> do_i vs hm g i) il


(** Instruction *)
and do_i vs hm g (ins : Cil.instr) =
 match ins with
 | Set (lv, exp, _) ->
    let vset = Utils.sovv ~onlyNoOffset:true lv in
    if VS.cardinal vset = 1
    then
      begin
        let v = VS.min_elt vset in
        let fnexp = build g exp v  (vids_of_vs vs) in
        (** If any other state variable is used in the expression,
        replace it by its current function *)
        let used_in_f = VS.inter (vs_of_fexp vs fnexp) vs in
        let olde =
          try
            IH.find hm v.vid
          with Not_found ->  Empty v in
        let nexp = let_in_func v olde fnexp in
        if !debug then
          Printf.printf "Replacing %s\n by %s\n"
            (string_of_prefunc olde) (string_of_prefunc nexp);
        IH.replace hm v.vid nexp
      end
    else ()
 | _ -> ()


(** Block -> list of statements *)
and do_b vs hm g b =
  List.iter (fun s -> do_s vs hm g s) b.bstmts

(** Statements *)
and do_s vs hm g stm =
  match stm.skind with
    Instr il ->
      do_il vs hm g il
  | If (e, b1, b2, _) ->
     ppe e;
     let cond1 = gcompose g (GCond (e, GEmpty)) in
     do_b vs hm cond1 b1;
     ppe (neg_exp e);
     if non_empty_block b2 then 
       let cond2 = gcompose g (GCond ((neg_exp e), GEmpty)) in
       do_b vs hm cond2 b2;
  | Loop (b, _ ,_, _) ->
     begin
       try
         let igu = (IH.find !loops stm.sid).Cloop.loopIGU in
         let forlp = gcompose g (GFor (checkOption igu, GEmpty)) in
         do_b vs hm forlp b
       with
         Not_found -> raise (Failure "Found a loop statement not in \
 the program loops.")
     end
  | Block b -> do_b vs hm g b
  | _ -> ()


let prefunc stmtlist statevs =
  if !debug then print_endline "---Transform to SSA---";
  let assignments = IH.create 10 in
  List.iter (fun s -> do_s statevs assignments GEmpty s) stmtlist;
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
      let stateVars = outer_join_lists
	    (match cl.Cloop.rwset with (r, w, rw) -> w, rw) in
      let vars = vs_of_defsMap cl.Cloop.definedInVars in
      let stateSet = subset_of_list stateVars vars in
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
        body = prefunc body_stmts stateSet;
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
