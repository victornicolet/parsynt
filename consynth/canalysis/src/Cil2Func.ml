open Utils
open Cil
open Format
open Loops
open PpHelper


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
(**
    LetState is used for the reduction, it allows us to simplify
    the sequence of let ... in .. into a shorter sequence
    when several let x = .. in .. assign different variables.
 *)
  | LetState of letin * letin

and expr =
  | Var of varinfo
  | Container of exp * substitutions
  | FQuestion of exp * expr * expr

and substitutions = expr IM.t

let rec wf_letin =
  function
  | State (vs, emap) -> true
  | Let (vi, expr, letin, loc) -> true
  | LetCond (c, let_if, let_else, let_cont, loc) -> true
  | LetRec ((i, g, u), let_body, let_cont, loc) -> true
  | LetState (def_state, let_cont) ->
     begin
       match def_state with
       | State (vs, emap) -> wf_letin def_state
       | _ -> false
     end

let empty_state vs = State (vs, IM.empty)

let is_enpty_state state =
  match state with
  | State (vs, emap) when IM.is_empty emap -> true
  | _ -> false

(**
   Convert a let-in form of a loop body into
   an expression if possible. The conversion is
   performed when :
   - only one variable is modified in the loop body
   (without conisdering the index)
   - (* TODO *) inlining expressions and splitting
   loops for each written variable is not too expensive.
*)

let convert_loop let_body = ()


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

  | _ -> failwith "Construct not allowed while building expressions"


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

  | Call (lvo, ef, e_argli, loc) ->
     failwith "call not supported"

  | _ -> failwith "form not supported"

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
     let if_fun = LetCond (e, block_then, block_else, empty_state vs, loc) in
     let_add let_form if_fun

  | Loop (b, loc,_,_) ->
     let block_loop = do_b vs b in
     let igu = checkOption ((IH.find !loops s.sid).Cloop.loopIGU) in
     let loop_fun = LetRec (igu, block_loop, empty_state vs, loc) in
     let_add let_form loop_fun

  | Block b ->
     let_add let_form (do_b vs b)

  | _ ->
     failwith "Statement unsupported in CPS conversion"


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
               let cur_var = Var (VSOps.getVi vid vs_if) in
               match if_expr_o, else_expr_o with
               | Some if_expr, Some else_expr ->
                  Some (FQuestion (c, if_expr, else_expr))

               | Some if_expr, None ->
                  Some
                    (FQuestion
                       (c, if_expr, cur_var))

               | None, Some else_expr->
                  Some
                    (FQuestion
                       (c, cur_var, else_expr))
               | None, None -> None
             )
             subs_if
             subs_else
         in
         true, State (vs_if, new_subs)
       end
     else
       false, let_if
  | _ -> false, let_if



(**
   The main goal of this reduction is to simplify the form by
   eliminating lets as much as possible, an handle specifically
   the if/else branches by merging their expressions if possible.

   For a fully "reducible" loop body, the result if a maaping
   from variable ids to expressions with conditionals inside.
*)

let rec red let_form substs =
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
     red cont nsubs
  | LetRec (igu, body, cont, loc) ->
     let redd_body = reduce body in
     LetRec (igu, redd_body, reduce cont, loc)
  | LetCond (e, bif, belse, cont, loc) ->
     let red_if = reduce bif in
     let red_else = reduce belse in
     let red_cont = reduce cont in
     let merged, exprs = merge_cond e red_if red_else in
     if merged
     then exprs
     else LetCond (e, red_if, red_else, red_cont, loc)
  | LetState (state, let_cont) ->
     LetState (state,reduce let_cont)

and reduce let_form = red let_form IM.empty


(**
   MAIN ENTRY POINT
 *)

let cil2func block statevs =
  if !debug then eprintf "-- Cil --> Functional --";
  let let_expression = do_b statevs block in
  reduce let_expression


(** Pretty-printinf functions *)
let rec pp_letin ppf =
  function
  | State (vs, expr_map) ->
     if IM.is_empty expr_map then
       fprintf ppf "@[{%a}@]"
         VSOps.pvs vs
     else
       fprintf ppf "@[{%a ::@. %a}@]@."
         VSOps.pvs vs
         (ppimap pp_expr) expr_map

  | Let (vi, expr, letn, loc) ->
     fprintf ppf "@[%slet%s %s = %a@]@[%sin%s  %a @]@."
       (color "red") default vi.vname pp_expr expr
       (color "red") default
       pp_letin letn

  | LetRec ((i, g , u), let1, letcont, loc) ->
     fprintf ppf "%sletrec%s (%s,%s,%s) @; %a@]@[%sin%s @[ %a @]"
       (color "red") default
       (psprint80 Cil.dn_instr i) (psprint80 Cil.dn_exp g)
       (psprint80 Cil.dn_instr u)
       pp_letin let1
       (color "red") default
       pp_letin letcont

  | LetCond (exp, letif, letelse, letcont, loc) ->
     fprintf ppf "@[%sif%s %s @]@[%sthen%s %a @]@[%selse%s %a @]%sendif%s@[%a@]"
       (color "red") default
       (psprint80 Cil.dn_exp exp)
       (color "red") default
       pp_letin letif
       (color "red") default
       pp_letin  letelse
       (color "red") default
       pp_letin letcont

  | LetState (let_state, let_cont) ->
      fprintf ppf "@[%slet%s %a@]@[%sin%s  %a @]@."
        (color "red") default
        pp_letin let_state
        (color "red") default
        pp_letin let_cont


and pp_expr ppf =
  function
    | Var vi -> fprintf ppf "%s%s%s" (color "yellow") vi.vname default

    | Container (e, subs) ->
       if IM.is_empty subs then
         fprintf ppf "%s"
           (psprint80 Cil.dn_exp e)
       else
       fprintf ppf "%s [%a]"
         (psprint80 Cil.dn_exp e)  (ppimap pp_expr) subs

    | FQuestion (c, a, b) ->
       fprintf ppf "(%s ? %a : %a)"
         (psprint80 Cil.dn_exp c) pp_expr a pp_expr b

let printlet letform = pp_letin std_formatter letform
let eprintlet letform = pp_letin err_formatter letform
let sprintlet letform = pp_letin str_formatter letform ; flush_str_formatter ()
