open Cil
open Utils
open Loops

module IH = Inthash

let debug = ref false
(** The loops in the files *)
let loops = IH.create 10

type guard =
    GEmpty 
  | GCond of Cil.exp * guard
  | GFor of Loops.forIGU * guard


let rec gCompose g1 g2 =
  match g1 with
  | GEmpty -> g2
  | GCond (e, g) -> GCond (e, gCompose g g2)
  | GFor (igu, g) -> GFor (igu, gCompose g g2)

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
  | ForLoop of Loops.forIGU * Cil.exp list * preFunc
  (* An expression guarded by an if *)
  | Guarded of preFunc * preFunc * preFunc

let rec build_expr ?(subs= [])  g (expr : Cil.exp) (x : Cil.varinfo)=
  match g with
  | GEmpty -> Container expr
  | GCond (e, g') -> Guarded (Container e, 
                              (build_expr g' expr x),
                              Container (v2e x))
  | GFor (igu, g') -> ForLoop (igu, subs, build_expr g' expr x)


let rec rep vid old ne =
  match ne with
  | Empty -> Empty
  | Container e -> (rep_in_e vid old e)
  | FBinop (op, e1, e2) -> FBinop (op, rep vid old e1, rep vid old e2)
  | FUnop (op, e) -> FUnop (op, rep vid old e)
  | ForLoop (e, el, g) -> ForLoop (e, el, rep vid old g)
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
          with Not_found -> Empty in
        let nexp = replace_init_in v.vid olde fexp in
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
     let cond2 = gCompose g (GCond (e, GEmpty)) in
     do_b hm cond2 b2
  | Loop (b, _ ,_, _) ->
     begin
       try
         let igu = (IH.find loops stm.sid).Cloop.loopIGU in
         let forlp = gCompose g (GFor (checkOption igu, GEmpty)) in
         do_b hm forlp b
       with
         Not_found -> raise (Failure "Found a loop statement not in \
 the program loops.")
     end
  | Block b -> do_b hm g b
  | _ -> ()


let ssaify stmtlist statevars =
  let assignments = IH.create 10 in
  List.iter
    (fun vid -> IH.add assignments vid Empty) 
    statevars;
  List.iter (fun s -> do_s assignments GEmpty s) stmtlist

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


let processLoop (sid : int) (cl : Cloop.t) =
  let stateVars = Utils.outer_join_lists
	(match cl.Cloop.rwset with (r, w, rw) -> w, rw) in
  let loopIndex = indexOfIGU  (checkOption cl.Cloop.loopIGU) in
  removeIGU cl.Cloop.loopStatement (checkOption cl.Cloop.loopIGU);
  if !debug then pps cl.Cloop.loopStatement;
  ()


(** Main entry point *)

let processFile_l2s lps =
  IH.copy_into loops lps;
  IH.iter processLoop loops
