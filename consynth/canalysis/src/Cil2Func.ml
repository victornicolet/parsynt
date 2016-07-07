open Utils
open Cil
open Format
open Loops

(**
   Implementatoni of a simple CPS comversion from the
   Cil program to a let-forms program with conditonals
   and loops.
   The loops can be translated in a straightforawrd
   manner to a recursive function.
*)


let debug = ref false
(** The loops in the files *)
let loops = ref (IH.create 10)


type letin =
  | State of VS.t
  | Let of varinfo * expr * letin * location
  | LetRec of Loops.forIGU * letin * letin * location
  | LetCond of exp * letin * letin * letin * location

and expr =
  | Var of varinfo
  | Container of exp * substitutions

and substitutions = (int * expr) list


(**
   Add a new let-form at the end of an old one,
   terminated by the state.
*)

let rec let_add old_let new_let =
  match old_let with
  | State vs -> new_let

  | Let (v, e, olet, lc) ->
     Let (v, e, let_add olet new_let, lc)

  | LetCond (e, bif, belse, cont, lc) ->
     LetCond (e, bif, belse, let_add cont new_let, lc)

  | LetRec (igu, letform, let_cont, lc) ->
     LetRec (igu, letform, let_add let_cont new_let, lc)


let rec do_il vs il =
  List.fold_left (do_i vs) (State vs) il

and do_i vs let_form =
  function
  | Set (lv, exp, loc) ->
     let vset = VSOps.sovv ~onlyNoOffset:true lv in
     if VS.cardinal vset = 1 then
       let lh_var = VS.max_elt vset in
       let e = Container (exp, []) in
       let_add let_form (Let (lh_var, e, State vs, loc))
     else
       raise (Failure "do_il : set with left-hand side varaibles amount != 1")

  | Call (lvo, ef, e_argli, loc) -> State vs

  | _ -> State vs

and do_b vs b =
  List.fold_left (do_s vs) (State vs) b.bstmts

and do_s vs let_form s =
  match s.skind with
  | Instr il ->
     let instr_fun = do_il vs il in
     let_add let_form instr_fun
  | If (e, b1, b2, loc) ->
     let block_then = do_b vs b1 in
     let block_else = do_b vs b2 in
     let if_fun = LetCond (e, block_else, block_then, State vs, loc) in
     let_add let_form if_fun
| Loop (b, loc,_,_) ->
   let block_loop = do_b vs b in
   let igu = checkOption ((IH.find !loops s.sid).Cloop.loopIGU) in
   let loop_fun = LetRec (igu, block_loop, State vs, loc) in
   let_add let_form loop_fun
| Block b -> let_add let_form (do_b vs b)
| _ -> failwith "Statement unsupported in CPS conversion"
