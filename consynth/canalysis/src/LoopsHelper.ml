open Cil
open Utils
open ListTools
module EC = Expcompare

let debug = ref false

type forIGU = (Cil.instr * Cil.exp * Cil.instr)

let removeFromCFG (stm : stmt) =
  let succs = stm.succs in
  let preds = stm.preds in
  let eq_stm s = (stm.sid = s.sid) in
  List.iter (fun s -> (s.succs <- List.filter eq_stm s.succs)) preds;
  List.iter (fun s -> (s.preds <- List.filter eq_stm s.preds)) succs

let rec remLastInstr (bdy : stmt list) =
  if List.length bdy < 1
  then None, None
  else
    let lastStmt = last bdy in
    match lastStmt.skind with
    | Instr il ->
       begin
         match il with
         | [i] ->
            begin
              removeFromCFG lastStmt;
              let stmtli = (remove_last bdy) in
              Some i, Some stmtli
            end

         | hd::tl ->
            begin
              lastStmt.skind <- Instr (remove_last il);
              Some (last il), Some bdy
            end

         | [] -> None, None
       end

    | Block b -> remLastInstr b.bstmts

    | _ -> None, Some bdy



(** Check that two instructions are different *)
let rec instr_eq instr instr' =
  match instr, instr' with
  | Set (lv, e, loc), Set (lv', e', loc') ->
     (lval_eq lv lv') && (expr_eq e e')
  | Call (lvo, ef, el, loc), Call (lvo', ef', el',loc') ->
     (lvo = lvo') && (ef = ef') && (el = el')
  | _ , _ -> false

and lval_eq lval lval' =
  VS.equal (VSOps.sovv lval) (VSOps.sovv lval')

and expr_eq e e'=
  e = e'


(**
    When a loop contains an inner loop, we want to remove the index
    initialization from the body of the outer loop to reflect the
    original program, where the init statement is in the for statement.
*)

let rec removeInitInstr (bdy : stmt list) nbdy (init : instr) (inner : stmt)
    : stmt list =
  let rem_instr stmt =
    let stmtskind =
      if List.mem inner stmt.succs
      then
        begin
          match stmt.skind with
          | Instr il ->
             Instr (
               List.filter
                 (fun instr -> not (instr_eq instr init)) il)
          | _ -> stmt.skind
        end
      else
        stmt.skind
    in
    {stmt with skind = stmtskind}
  in
  List.map rem_instr bdy

(** Extracting the termination condition of the loop *)
let get_loop_condition b =
  (* returns the first non-empty
   * statement of a statement list *)
  (* stm list -> stm list *)
  let rec skipEmpty = function
    | [] -> []
    | {skind = Instr []; labels = []}::rest ->
	   skipEmpty rest
    | x -> x
  in
  (* stm -> exp option * instr list *)
  let rec get_cond_from_if if_stm =
    match if_stm.skind with
      If(e,tb,fb,_) ->
	    let e = EC.stripNopCasts e in
	    let tsl = skipEmpty tb.bstmts in
	    let fsl = skipEmpty fb.bstmts in
	    (match tsl, fsl with
	      {skind = Break _} :: _, [] -> Some e
	    | [], {skind = Break _} :: _ ->
	       Some(UnOp(LNot, e, intType))
	    | ({skind = If(_,_,_,_)} as s) :: _, [] ->
	       let teo = get_cond_from_if s in
	       (match teo with
	         None -> None
	       | Some te ->
		      Some(BinOp(LAnd,e,EC.stripNopCasts te,intType)))
	    | [], ({skind = If(_,_,_,_)} as s) :: _ ->
	       let feo = get_cond_from_if s in
	       (match feo with
	         None -> None
	       | Some fe ->
		      Some(BinOp(LAnd,UnOp(LNot,e,intType),
			             EC.stripNopCasts fe,intType)))
	    | {skind = Break _} :: _, ({skind = If(_,_,_,_)} as s):: _ ->
	       let feo = get_cond_from_if s in
	       (match feo with
	         None -> None
	       | Some fe ->
		      Some(BinOp(LOr,e,EC.stripNopCasts fe,intType)))
	    | ({skind = If(_,_,_,_)} as s) :: _, {skind = Break _} :: _ ->
	       let teo = get_cond_from_if s in
	       (match teo with
	         None -> None
	       | Some te ->
		      Some(BinOp(LOr,UnOp(LNot,e,intType),
			             EC.stripNopCasts te,intType)))
	    | ({skind = If(_,_,_,_)} as ts) :: _ ,
           ({skind = If(_,_,_,_)} as fs) :: _ ->
	       let teo = get_cond_from_if ts in
	       let feo = get_cond_from_if fs in
	       (match teo, feo with
	         Some te, Some fe ->
		       Some(BinOp(LOr,BinOp(LAnd,e,EC.stripNopCasts te,intType),
			              BinOp(LAnd,UnOp(LNot,e,intType),
				                EC.stripNopCasts fe,intType),intType))
	       | _,_ -> None)
	    | _, _ -> (if !debug
          then ignore(E.log "cond_finder: branches of %a not good\n"
					                       d_stmt if_stm);
		           None))
    | _ -> (if !debug
      then ignore(E.log "cond_finder: %a not an if\n" d_stmt if_stm);
	        None)
  in
  let sl = skipEmpty b.bstmts in
  match sl with
    ({skind = If(_,_,_,_); labels=[]} as s) :: rest ->
      get_cond_from_if s, rest
  | s :: _ ->
     (if !debug then ignore(E.log "checkMover: %a is first, not an if\n"
			                  d_stmt s);
      None, sl)
  | [] ->
     (if !debug then ignore(E.log "checkMover: no statements in loop block?\n");
      None, sl)


(** Get the initiatlization, termination and update in a*)
let get_loop_IGU loop_stmt : (forIGU option * Cil.stmt list) =
  match loop_stmt.skind with
  | Loop (bdy, _, _, _) ->
     begin
       try
         let body_copy = Cil.mkBlock bdy.bstmts in
         (**
             Identify the termiation condition and remove the break
             statement associated to it.
         *)
         let term_expr_o, rem = get_loop_condition body_copy in
         let term_expr = match term_expr_o with
           | Some expr ->
              expr
           | None ->
              raise (Failure "couldn't get the termination condition.")
         in
         let init = lastInstr (List.nth loop_stmt.preds 1) in
         (** Removing the last instruction **should** remove the index update *)
         let update, newbody =
           match  remLastInstr rem with
           | Some instr, Some s ->
              instr, s
           | None, Some s ->
              begin
                ppbk (Cil.mkBlock s);
                raise (Failure "failed to find last intruction.")
              end
           | Some _, None
           | None, None ->
              raise (Failure "failed to find last statement in body.")
         in
         Some (init, (neg_exp term_expr), update), newbody
       with Failure s ->
		 print_endline ("get_loop_IGU : "^s); None , bdy.bstmts
     end
  |_ ->
     raise(
       Failure(
         "get_loop_IGU : bad argument, expected a Loop statement."))
