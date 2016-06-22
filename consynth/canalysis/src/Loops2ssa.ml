open Cil
open Utils
open Loops
open Printf

module IH = Inthash
module VS = Utils.VS

let debug = ref false
(** The loops in the files *)
let loops = ref (IH.create 10)


(** ------------------------------------------------------------------*)
(** Type for intermediary representation of the loop body *)
(** The loop body is a Inthash from the state variable ids 
    to an expression of type preFunc *)
(** Short functional representation *)
type preFunc = 
  | Empty
  (** A cil expression *)
  | Container of Cil.exp
  | FBinop of Cil.binop * preFunc * preFunc
  | FUnop of Cil.unop * preFunc
  (** 
      A loop enclosing an assignment is reduced to the IGU,
      the subscripts if is is an array and the right-hand side
      expression in the assignment.
      The subscript expression list is empty if it is a scalar.
  *)
  (** init, igu, subscripts, expression *)
  | ForLoop of preFunc * Loops.forIGU * Cil.exp list * preFunc
  (* An expression guarded by an if *)
  | Guarded of preFunc * preFunc * preFunc

(** 
    Some types to record the control statements above 
    an expression
 *)
type guard =
    GEmpty 
  | GCond of Cil.exp * guard
  | GFor of Loops.forIGU * guard


(** ------------------------------------------------------------------*)
(** Utilities for the types *)

let rec gCompose g1 g2 =
  match g1 with
  | GEmpty -> g2
  | GCond (e, g) -> GCond (e, gCompose g g2)
  | GFor (igu, g) -> GFor (igu, gCompose g g2)


let rec ps_pf pf =
  match pf with
  | Empty -> "Empty"
  | Container e -> (psprint80 Cil.d_exp e)
  | FBinop (op, e1, e2) -> 
     String.concat " " [ (ps_pf e1); (psprint80 Cil.d_binop op); (ps_pf e2)]
  | FUnop (op, e) ->
     String.concat " " [(psprint80 Cil.d_unop op); (ps_pf e)]
  | ForLoop (e0, (i, g, u), el, e) ->
     String.concat " "  ([ "Init: "^(ps_pf e0)^"\nFor {"; 
                           (psprint80 Cil.d_instr i);
                           (psprint80 Cil.d_exp g); 
                           (psprint80 Cil.d_instr u);
                           "[:"]@
                            (List.map (fun e -> (psprint80 Cil.d_exp e)) el)@
                            [":]\n"; ps_pf e; "}"])

  | Guarded (c, e1, e2) -> 
     "("^(ps_pf c)^" ? "^(ps_pf e1)^" : "^(ps_pf e2)^")"


let rec build_expr ?(subs= [])  g (expr : Cil.exp) (x : Cil.varinfo)=
  match g with
  | GEmpty -> Container expr
  | GCond (e, g') -> Guarded (Container e, 
                              (build_expr g' expr x),
                              Container (v2e x))
  | GFor (igu, g') -> 
     ForLoop (Container (v2e x), igu, subs, build_expr g' expr x)


let rec rep vid old ne =
  match ne with
  | Empty -> Empty
  | Container e -> (rep_in_e vid old e)
  | FBinop (op, e1, e2) -> FBinop (op, rep vid old e1, rep vid old e2)
  | FUnop (op, e) -> FUnop (op, rep vid old e)
  | ForLoop (init, e, el, g) -> ForLoop (rep vid old init, e, el, g)
  | Guarded (e, g1, g2) -> Guarded (e, rep vid old g1,
                                    rep vid old g2)

and rep_in_e vid old_expr cont_e =
  match cont_e with
  | BinOp (op, e1, e2, loc) -> 
     let e1' = rep_in_e vid old_expr e1 in
     let e2' = rep_in_e vid old_expr e2 in
     FBinop (op, e1', e2')
  | Question (c, e1, e2, loc) ->
     let c' = rep_in_e vid old_expr c in
     let e1' = rep_in_e vid old_expr e1 in
     let e2' = rep_in_e vid old_expr e2 in
     Guarded (c', e1', e2')
  | UnOp (op, e, loc) ->
     let e' = rep_in_e vid old_expr e  in
     FUnop (op, e')
  | Lval (h, o) ->
     begin
       match h with
       | Var x -> if x.vid = vid then old_expr else Container cont_e
       | _ -> Container cont_e
     end
  |_ -> Container cont_e


let rec replace_init_in vid old_expr new_expr =
  rep vid old_expr new_expr

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
        let fexp = build_expr g exp v in
        let olde = 
          try
            IH.find hm v.vid 
          with Not_found -> Container (v2e v) in
        let nexp = replace_init_in v.vid olde fexp in
        if !debug then
          Printf.printf "Replacing %s\n by %s\n"
            (ps_pf olde) (ps_pf nexp);
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
     let cond1 = gCompose g (GCond (e, GEmpty)) in
     do_b hm cond1 b1; 
     let cond2 = gCompose g (GCond ((neg_exp e), GEmpty)) in
     do_b hm cond2 b2
  | Loop (b, _ ,_, _) ->
     begin
       try
         let igu = (IH.find !loops stm.sid).Cloop.loopIGU in
         let forlp = gCompose g (GFor (checkOption igu, GEmpty)) in
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
      IH.iter (fun i v -> printf "%i = %s\n" i (ps_pf v)) assignments;
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
      if cloop.Cloop.hasBreaks 
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