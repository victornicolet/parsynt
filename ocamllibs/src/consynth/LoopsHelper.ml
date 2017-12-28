open Cil
open Utils
open VariableAnalysis
open ListTools
module EC = Expcompare
module Ct = CilTools
module VS = Utils.VS
module E = Errormsg

let debug = ref false

type igu = (Cil.instr * Cil.exp * Cil.instr)

type loop_info = {
  lid : int;
  initial_values : Cil.constant IM.t;
  added_vars : VS.t;
  index : Cil.varinfo list;
  array_access : int;
}

let rem_stmt_in_cfg (stm : stmt) =
  let succs = stm.succs in
  let preds = stm.preds in
  let eq_stm s = (stm.sid = s.sid) in
  List.iter (fun s -> (s.succs <- List.filter eq_stm s.succs)) preds;
  List.iter (fun s -> (s.preds <- List.filter eq_stm s.preds)) succs

let rec rem_last_instr (bdy : stmt list) =
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
              rem_stmt_in_cfg lastStmt;
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

    | Block b -> rem_last_instr b.bstmts

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
  VS.equal (VS.sovv lval) (VS.sovv lval')

and expr_eq e e'=
  e = e'

let instr_in instrlist instr =
  List.exists (instr_eq instr) instrlist


(** Is the read-write set empty *)
let is_empty_state (r, w) =
  VS.is_empty w

(**
    When a loop contains an inner loop, we want to remove the index
    initialization from the body of the outer loop to reflect the
    original program, where the init statement is in the for statement.
   @param bdy : the block to be modified.
   @param init : the init statement to remove.
   @param inner : the loop statement of the inner loop.
*)

let rec rem_loop_init (bdy : block) inners :
  block =
  let rem_instr (init, inner) stmt =
    let stmtkind =
      if List.mem inner.sid (List.map (fun stmt -> stmt.sid) stmt.succs)
      then
        begin
          Format.printf "In succs.@.";
          match stmt.skind with
          | Instr il ->
             Instr (
               List.filter
                 (fun instr -> not (instr_eq init instr)) il)
          | _ -> stmt.skind
        end
      else
        stmt.skind
    in
    {stmt with skind = stmtkind}
  in
  { bdy with bstmts = List.map (List.fold_right rem_instr inners) bdy.bstmts }

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
let get_loop_IGU loop_stmt : (igu option * Cil.stmt list) =
  match loop_stmt.skind with
  | Loop (bdy, _, _, _) ->
     begin
       try
         let body_copy = Cil.mkBlock bdy.bstmts in
         (**
             Identify the termination condition and remove the break
             statement associated to it.
         *)
         let term_expr_o, rem = get_loop_condition body_copy in
         let term_expr = match term_expr_o with
           | Some expr ->
              expr
           | None ->
              raise (Failure "couldn't get the termination condition.")
         in
         let init =
           if List.length loop_stmt.preds < 2 then
             ( Format.printf "Did you compute the CFG information before \
                       calling get_loop_IGU?@.";
               None)
           else
             Some (last_instr (List.nth loop_stmt.preds 1)) in
         (** Removing the last instruction **should** remove the index update *)
         let update, newbody =
           match  rem_last_instr rem with
           | Some instr, Some s ->
              instr, s
           | None, Some s ->
              begin
                Ct.ppbk (Cil.mkBlock s);
                raise (Failure "failed to find last intruction.")
              end
           | Some _, None
           | None, None ->
              raise (Failure "failed to find last statement in body.")
         in
         Some (check_option init, (Ct.neg_exp term_expr), update), newbody
       with Failure s ->
		 print_endline ("get_loop_IGU : "^s); None , bdy.bstmts
     end
  |_ ->
     raise(
       Failure(
         "get_loop_IGU : bad argument, expected a Loop statement."))


let mkcond expr_list =
  List.fold_left
    (fun c nc -> BinOp (Cil.BAnd, c, nc, TInt (IBool, [])))
    (Cil.Const (Cil.CInt64 (Int64.of_int 1, Cil.IBool, None)))
    expr_list

let search_loop_exits loop_statement body =
  let rec aux (cond_stack, breaks) stm =
    match stm.skind with
    | If (c, sif, selse, loc) ->
       let _, breaks_if =
         List.fold_left aux (cond_stack@[c], []) sif.bstmts
       in
       let _, breaks_else =
         List.fold_left
           aux (cond_stack@[CilTools.neg_exp c], []) selse.bstmts
       in
       (cond_stack, breaks@breaks_if@breaks_else)

    | Break _ ->
       (cond_stack, breaks@[(stm,mkcond cond_stack)])

    | Block b
    | Loop (b, _, _, _) ->
       List.fold_left aux (cond_stack, []) b.bstmts
    | Goto (stmtr, _) -> (cond_stack, breaks)
    | _ -> (cond_stack, breaks)
  in
  List.fold_left  aux ([],[]) body


exception Init_with_temp of varinfo

let rec valid_init_expr cil_exp =
  match cil_exp with
  | Cil.Const c ->  true
  | Cil.Lval (h, o) ->
    (match h with
     | Cil.Var vi ->
       if vi.vistmp then
         raise (Init_with_temp vi)
       else true

     | Cil.Mem (Cil.BinOp (_, Cil.Lval ((Cil.Var vi), Cil.NoOffset), e,_)) ->
       valid_init_expr e

     | _ -> false)

  | _ -> false



(* Can raise Init_with_temp *)
let reduce_def_to_const vid stmt =
  let aux_for_instr vid instr =
    match instr with
    | Set (lv, e, _) ->
       let vi = VS.max_elt (basic lv) in
       if vi.vid = vid
       then (if valid_init_expr e then Some e else None)
       else None
    | _ -> None
  in
  match stmt.skind with
  | Instr il ->
     let l = List.filter is_some (List.map (aux_for_instr vid) il) in
     (match l with | [c] -> c | _ -> None)
  | _ -> None
