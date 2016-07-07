open Utils
open Cil
open Format
open Loops

module IM = Map.Make(struct type t = int let compare = compare end)

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
  | State of VS.t * (expr IM.t)
  | Let of varinfo * expr * letin * location
  | LetRec of Loops.forIGU * letin * letin * location
  | LetCond of exp * letin * letin * letin * location

and expr =
  | Var of varinfo
  | Container of exp * substitutions
  | FQuestion of exp * expr * expr

and substitutions = expr IM.t

let empty_state vs = State (vs, IM.empty)

let rec apply_subs expr subs =
  match expr with
  | Var vi ->
     (try IM.find vi.vid subs with Not_found -> expr)

  | Container (e, subs') ->
     Container (e,
                IM.merge
                  (fun i ao bo ->
                  match ao with
                  | Some a -> Some a
                  | None -> bo)
                  subs
                  subs')

  | FQuestion (e, e1, e2) ->
     FQuestion (e, apply_subs e1 subs, apply_subs e2 subs)

(**
   Add a new let-form at the end of an old one,
   terminated by the state.
*)

let rec let_add old_let new_let =
  match old_let with
  | State (vs, subs) ->
     if IM.is_empty subs then
       new_let
     else
       failwith "Substitutions should be empty while bulding let-forms"
  | Let (v, e, olet, lc) ->
     Let (v, e, let_add olet new_let, lc)

  | LetCond (e, bif, belse, cont, lc) ->
     LetCond (e, bif, belse, let_add cont new_let, lc)

  | LetRec (igu, letform, let_cont, lc) ->
     LetRec (igu, letform, let_add let_cont new_let, lc)


let rec do_il vs il =
  List.fold_left (do_i vs) (empty_state vs) il

and do_i vs let_form =
  function
  | Set (lv, exp, loc) ->
     let vset = VSOps.sovv ~onlyNoOffset:true lv in
     if VS.cardinal vset = 1 then
       let lh_var = VS.max_elt vset in
       let e = Container (exp, IM.empty) in
       let_add let_form (Let (lh_var, e, (empty_state vs), loc))
     else
       raise (Failure "do_il : set with left-hand side variables amount != 1")

  | Call (lvo, ef, e_argli, loc) -> empty_state vs

  | _ -> empty_state vs

and do_b vs b =
  List.fold_left (do_s vs) (empty_state vs) b.bstmts

and do_s vs let_form s =
  match s.skind with
  | Instr il ->
     let instr_fun = do_il vs il in
     let_add let_form instr_fun
  | If (e, b1, b2, loc) ->
     let block_then = do_b vs b1 in
     let block_else = do_b vs b2 in
     let if_fun = LetCond (e, block_else, block_then, empty_state vs, loc) in
     let_add let_form if_fun
  | Loop (b, loc,_,_) ->
     let block_loop = do_b vs b in
     let igu = checkOption ((IH.find !loops s.sid).Cloop.loopIGU) in
     let loop_fun = LetRec (igu, block_loop, empty_state vs, loc) in
     let_add let_form loop_fun
  | Block b -> let_add let_form (do_b vs b)
  | _ -> failwith "Statement unsupported in CPS conversion"


(** Reduction and simplification of expressions and lets *)

let merge_cond c let_if let_else =
  match let_if, let_else with
  | State (vs_if, subs_if) , State (vs_else, subs_else) ->
     if VS.equal vs_if vs_else
     then
       begin
         let new_subs =
           IM.merge
             (fun vid if_expr_o else_expr_o ->
               match if_expr_o, else_expr_o with
               | Some if_expr, Some else_expr ->
                  Some (FQuestion (c, if_expr, else_expr))
               | Some if_expr, _ -> Some if_expr
               | _, _ -> None )
             subs_if
             subs_else
         in
         true, State (vs_if, new_subs)
       end
     else
       false, let_if
| _ -> false, let_if


let rec reduce let_form substs =
  match let_form with
  | State (vs, im) ->
     let id_list = VSOps.vids_of_vs vs in
     let final_state_exprs =
       IM.filter (fun k v -> List.mem k id_list) substs
     in
     State (vs, final_state_exprs)

  | Let (vi, expr, cont, _) ->
     let nexpr = apply_subs expr substs in
     let nsubs = IM.add vi.vid nexpr substs in
     reduce cont nsubs
  | LetRec (igu, body, cont, loc) ->
     LetRec (igu, red body, red cont, loc)
  | LetCond (e, bif, belse, cont, loc) ->
     let red_if = red bif in
     let red_else = red belse in
     let merged, exprs = merge_cond e red_if red_else in
     if merged
     then exprs
     else LetCond (e, red bif, red belse, red cont, loc)

and red let_form = reduce let_form IM.empty
