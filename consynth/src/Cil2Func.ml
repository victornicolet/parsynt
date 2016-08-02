open Cil
open Format
open Loops
open Utils
open Utils.CilTools
open PpHelper
open SketchTypes
open SPretty

(**
   Implementation of a simple CPS comversion from the
   Cil program to a let-forms program with conditonals
   and loops.
   The loops can be translated in a straightforawrd
   manner to a recursive function.
*)


let debug = ref false
(** The loops in the files *)
let loops = ref (IM.empty)

let uses = ref (IH.create 10)
let add_uses id vs = IH.add !uses id vs

let __letin_index = ref 0
let gen_id () = incr __letin_index; !__letin_index

type letin =
  | State of (expr IM.t)
  | Let of varinfo * expr * letin * int * location
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
  | Array of varinfo * (expr list)
  | Container of exp * substitutions
  | FunApp of exp * (expr list)
  | FQuestion of exp * expr * expr
  | FRec of Loops.forIGU * expr
  (** Types for translated expressions *)
  | FBinop of symb_binop * expr * expr
  | FUnop of symb_unop * expr
  | FConst of constants
  | FSizeof of typ
  | FSizeofE of expr
  | FSizeofStr of string
  | FAlignof of typ
  | FAlignofE of expr
  | FCastE of typ * expr
  | FAddrof of lval
  | FAddrofLabel of stmt ref
  | FStartOf of lval

and substitutions = expr IM.t



(**
   Check well-formedness of let-in forms. The two main points are
   that the only subsitutions occur for state-variables (the are
   defined as the only variables we write in, in the loop body)
   and the specific def-state construct must contain a state as its
   first component.
*)
let rec wf_letin vs =
  function
  | State emap ->
     (IM.fold
       (fun k v ok -> ok && (VSOps.hasVid k vs)) emap true)

  | Let (vi, expr, letin, id, loc) -> wf_letin vs letin

  | LetCond (c, let_if, let_else, let_cont, loc) ->
     wf_letin vs let_if && wf_letin vs let_else && wf_letin vs let_cont

  | LetRec ((i, g, u), let_body, let_cont, loc) ->
     wf_letin vs let_body && wf_letin vs let_cont

  | LetState (def_state, let_cont) ->
     let wf_def_state =
       match def_state with
       | State emap -> wf_letin vs def_state
       | _ -> false
     in
     wf_def_state && wf_letin vs let_cont

let rec transform_topdown funct letin =
  let letin' = funct letin in
  match letin' with
  | Let (vi, expr, cont, id, loc) ->
     Let (vi, expr, transform_topdown funct cont, id, loc)

  | LetCond (c, let_if, let_else, let_cont, loc) ->
     LetCond (c, transform_topdown funct let_if,
              transform_topdown funct let_else,
              transform_topdown funct let_cont,
              loc)

  | LetRec ((i, g, u), let_body, let_cont, loc) ->
     LetRec ((i, g, u), transform_topdown funct let_body,
             transform_topdown funct let_cont, loc)

  | LetState (def_state, let_cont) ->
     LetState (def_state, transform_topdown funct let_cont)

  | _ -> letin'

let rec transform_bottomup funct letin =
  let applied_in =
    match letin with
    | Let (vi, expr, letin, id, loc) ->
       Let (vi, expr, transform_bottomup funct letin, id, loc)

    | LetCond (c, let_if, let_else, let_cont, loc) ->
       LetCond (c, transform_bottomup funct let_if,
                transform_bottomup funct let_else,
                transform_bottomup funct let_cont,
                loc)

    | LetRec ((i, g, u), let_body, let_cont, loc) ->
       LetRec ((i, g, u), transform_bottomup funct let_body,
               transform_bottomup funct let_cont, loc)

    | LetState (def_state, let_cont) ->
       LetState (def_state, transform_bottomup funct let_cont)

    | _ -> funct letin
  in
  funct applied_in


(** Helpers *)

let empty_state vs = State IM.empty

let container e = Container (e, IM.empty)

let rec is_not_identity_substitution vid expr =
  match expr with
  | Var (vi) -> vi.vid != vid
  | Container (e, subs) ->
     ((IM.fold
         (fun k v a -> (is_not_identity_substitution k v) || a)
         subs false)
      ||
        ((VS.max_elt (VSOps.sove e)).vid != vid))
  | _ -> true

let is_empty_state state =
  match state with
  | State emap ->
     (IM.is_empty emap) ||
       (IM.is_empty
          (IM.filter is_not_identity_substitution emap))

  | _ -> false

let remove_identity_subs substs =
  IM.filter is_not_identity_substitution substs


let rec apply_subs expr subs =
  match expr with
  | Var vi ->
     (try IM.find vi.vid subs with Not_found -> expr)

  | Array (vi, el) ->
     let vi_sub =
       (try
          let _ = IM.find vi.vid subs in
          raise (Failure (sprintf "Substitution for an array \
 violating one-assignment hypothesis : %s ." vi.vname))
        with Not_found -> vi) in
     Array (vi_sub, List.map (fun x -> apply_subs x subs) el)

  | Container (e, subs') ->
     Container (e,
                IM.merge
                  (fun i ao bo ->
                  match ao with
                  | Some a -> Some a
                  | None -> bo)
                  subs
                  subs')

  | FunApp (ef, el) ->
     FunApp (ef, List.map (fun e -> apply_subs e subs) el)

  | FQuestion (e, e1, e2) ->
     FQuestion (e, apply_subs e1 subs, apply_subs e2 subs)

  | FRec (igu, e) ->
     FRec (igu, apply_subs e subs)

  | _ -> failwith "Cannot apply substitutions for this expressions."


let rec used_vars_expr ?(onlyNoOffset = false) (exp : expr) =
  match exp with
  | Container (e, subs) ->
     let in_e = VSOps.sove e in
     let in_subs =
       IM.fold (fun k e vs -> VS.union vs (used_vars_expr e)) subs VS.empty in
     VS.union in_e in_subs

  | Var vi -> VS.singleton vi

  | Array (vi, subs) ->
     let in_subs =
       (if onlyNoOffset then
         VS.empty
       else
         List.fold_left
           (fun vs e -> VS.union vs (used_vars_expr e))
           VS.empty subs)
     in
     VS.add vi in_subs

  | FQuestion (c, e, e') ->
     let vc = VSOps.sove c in
     let ve = used_vars_expr ~onlyNoOffset:onlyNoOffset e in
     let ve' = used_vars_expr ~onlyNoOffset:onlyNoOffset e' in
     VS.union ve (VS.union ve' vc)

  | FAlignofE e
  | FSizeofE e
  | FCastE (_, e)
  | FUnop (_, e)
  | FRec (_, e) ->
     used_vars_expr ~onlyNoOffset:onlyNoOffset e

  | FBinop (op, e', e) ->
     let ve = used_vars_expr ~onlyNoOffset:onlyNoOffset e in
     let ve' = used_vars_expr ~onlyNoOffset:onlyNoOffset e' in
     VS.union ve ve'

  | _ -> VS.empty

let rec used_vars_letin ?(onlyNoOffset = false) (letform : letin) =
  match letform with
  | State substitutions ->
     IM.fold (fun k e vs -> VS.union vs (used_vars_expr e))
       substitutions VS.empty

  | Let (vi, e, cont, id, loc) ->
     VS.union (used_vars_expr e) (used_vars_letin cont)

  | LetCond (c, let_if, let_else, cont, loc) ->
     VSOps.unions
       [(VSOps.sove c);
        (used_vars_letin let_if);
        (used_vars_letin let_else);
        (used_vars_letin cont)]

  | LetRec (igu, let_body, cont, loc) ->
     VS.union (used_vars_letin let_body) (used_vars_letin cont)

  | LetState (state, cont) ->
     let in_subs = used_vars_letin state in
     VS.union in_subs (used_vars_letin cont)




(**
   Add a new let-form at the end of an old one,
   terminated by the state.
*)

let rec let_add old_let new_let =
 match old_let with
  | State subs ->
     if IM.is_empty subs then
       new_let
     else
       failwith "Substitutions should be empty while bulding let-forms"
  | Let (v, e, olet, id, lc) ->
     Let (v, e, let_add olet new_let, id, lc)

  | LetCond (e, bif, belse, cont, lc) ->
     LetCond (e, bif, belse, let_add cont new_let, lc)

  | LetRec (igu, letform, let_cont, lc) ->
     LetRec (igu, letform, let_add let_cont new_let, lc)

  | _ -> failwith "Construct not allowed while building expressions"

let rec do_il vs il =
  List.fold_left (do_i vs) (empty_state vs) il

and do_i vs let_form =
  let from_lval lv expre loc =
     let vset = VSOps.sovv ~onlyNoOffset:true lv in
     if VS.cardinal vset = 1 then
       let id = gen_id () in
       add_uses id (used_vars_expr expre);
       let lh_var = VS.max_elt vset in
       let_add let_form (Let (lh_var, expre, (empty_state vs), id, loc))
     else
       raise (Failure "do_il : set with left-hand side variables amount != 1")
  in
  function
  | Set (lv, exp, loc) ->
       from_lval lv (container exp) loc

  | Call (lvo, ef, e_argli, loc) ->
     begin
       match lvo with
       | Some lv ->
          let func_app =  FunApp (ef, (List.map container e_argli)) in
          from_lval lv func_app loc
       | _ -> failwith "Side effects not supported"
     end
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
     let igu =
     try
       check_option ((IM.find s.sid !loops).Cloop.loop_igu)
     with
       Not_found ->
         failwith (sprintf "Couldn't find loop %i." s.sid)
     in
     let loop_fun = LetRec (igu, block_loop, empty_state vs, loc) in
     let_add let_form loop_fun

  | Block b ->
     let_add let_form (do_b vs b)

  | _ ->
     eprintf "do_s : received unexpected Cil statement : @.@[<hov 4>%s@]@."
       (psprint80 Cil.d_stmt s);
     failwith "Statement unsupported in CPS conversion"



(** Reduction and simplification of expressions and lets *)

let merge_substs vs old_subs new_subs =
  let used_in_new_subs =
    (IM.fold (fun k v b -> VS.union b (used_vars_expr v))
       new_subs VS.empty)
  in
  if
           (* Check if the variables that are assigned in old_subs
              are used in new_subs *)
    (IMTools.is_disjoint ~non_empty:is_not_identity_substitution
       old_subs new_subs) &&
      not (IM.exists (fun k v -> VSOps.hasVid k used_in_new_subs)
             old_subs)
  then
    true, (IMTools.add_all old_subs new_subs), None
  else true, new_subs, Some (State old_subs)

(**
   Merge two conditions, if each branch is irreducible (already
   reduced to a single state) then tranform each substitution
   expression into a FQuestion (an expression instead of a lambda)
*)

let rec  merge_cond vs c let_if let_else pre_substs =
  match let_if, let_else with
  | State subs_if , State subs_else ->
     let new_subs =
       IM.merge
         (fun vid if_expr_o else_expr_o ->
           let cur_var = Var (VSOps.getVi vid vs) in
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
           | None, None -> None)
         subs_if
         subs_else
     in
     merge_substs vs pre_substs new_subs
  | _ -> false, pre_substs, None



(**
   Convert a let-in form of a loop body into
   an expression if possible. The conversion is
   performed when :
   - only one variable is modified in the loop body
   (without conisdering the index)
   - (* TODO *) inlining expressions and splitting
   loops for each written variable when not too expensive.
*)

and convert_loop vs let_body igu let_cont loc =
  match let_body with
  | State subs ->
     let subs' = remove_identity_subs subs in
     if (IM.cardinal subs') = 1
     then
       let vid, expr = IM.max_binding subs' in
       let rec_expr = FRec (igu, expr) in
       let id = gen_id () in
       add_uses id (used_vars_expr rec_expr);
       true,  Let (VSOps.getVi vid vs, rec_expr, let_cont, id, loc)
     else
       false, let_body

  | _ -> false, let_body



(**
   The main goal of this reduction is to simplify the form by
   eliminating lets as much as possible, an handle specifically
   the if/else branches by merging their expressions if possible.

   For a fully "reducible" loop body, the result if a maaping
   from variable ids to expressions with conditionals inside.
*)

and red vs let_form substs =
  match let_form with
  | State emap ->
     let id_list = VSOps.vids_of_vs vs in
     let final_state_exprs =
       IM.filter (fun k v -> List.mem k id_list) substs
     in
     State final_state_exprs

  | Let (vi, expr, cont, id, _) ->
     let nexpr = apply_subs expr substs in
     let nsubs = IM.add vi.vid nexpr substs in
     red vs cont nsubs

  | LetRec (igu, body, cont, loc) ->
     let redd_body = reduce vs body in
     let redd_cont = reduce vs cont in
     let converted, conversion =
       convert_loop vs redd_body igu redd_cont loc in
     if converted then
       conversion
     else
       LetRec (igu, redd_body, reduce vs  cont, loc)

  | LetCond (e, bif, belse, cont, loc) ->
     let red_if = reduce vs  bif in
     let red_else = reduce vs belse in
     let merged, prev_e, next_e = merge_cond vs e red_if red_else substs in
     if merged
     then
       (if Core.Std.is_none next_e
       then red vs cont prev_e
       else LetState (check_option next_e, red vs cont prev_e))
     else LetCond (e, red_if, red_else, reduce vs cont, loc)

  | LetState (state, let_cont) ->
     LetState (state, reduce vs let_cont)

and reduce vs let_form = red vs let_form IM.empty



(**
   MAIN ENTRY POINT
 *)
let init map_loops = loops := map_loops;;

let cil2func block statevs =
  (**
      We need the other loops in case of nested loops to avoid
      recomputing the for statement in the inner loops.
  *)
  if IM.cardinal !loops = 0 then
    failwith "You forgot to initialize the set of loops in Cil2Func ?";
  if !debug then eprintf "-- Cil --> Functional --";
  let let_expression = do_b statevs block in
  reduce statevs let_expression



(** Pretty-printing functions *)
let rec pp_letin ?(wloc = false) ppf (vs,letin) =
  match letin with
  | State expr_map ->
     if IM.is_empty expr_map then
       fprintf ppf "@[{%a}@]"
         VSOps.pvs vs
     else
       fprintf ppf "@[%a@]@."
         (ppimap pp_expr) expr_map

  | Let (vi, expr, letn, id, loc) ->
     fprintf ppf "@[%slet%s %s = %a@]@[%sin%s  %a @]%s@."
       (color "red") default vi.vname pp_expr expr
       (color "red") default
       (pp_letin ~wloc:wloc) (vs, letn)
       (if wloc then string_of_loc loc else "")

  | LetRec ((i, g , u), let1, letcont, loc) ->
     fprintf ppf "%sletrec%s (%s,%s,%s) @; %a@]@[%sin%s @[ %a @]%s"
       (color "red") default
       (psprint80 Cil.dn_instr i) (psprint80 Cil.dn_exp g)
       (psprint80 Cil.dn_instr u)
       (pp_letin ~wloc:wloc) (vs, let1)
       (color "red") default
       (pp_letin ~wloc:wloc) (vs, letcont)
       (if wloc then string_of_loc loc else "")

  | LetCond (exp, letif, letelse, letcont, loc) ->
     fprintf ppf
       "@[%sif%s %s @]@[%sthen%s %a @]@[%selse%s %a @]%sendif%s@[%a@]%s"
       (color "red") default
       (psprint80 Cil.dn_exp exp)
       (color "red") default
       (pp_letin ~wloc:wloc) (vs, letif)
       (color "red") default
       (pp_letin ~wloc:wloc)  (vs, letelse)
       (color "red") default
       (pp_letin ~wloc:wloc) (vs, letcont)
       (if wloc then string_of_loc loc else "")

  | LetState (let_state, let_cont) ->
     fprintf ppf "@[%slet%s %a@]@[%sin%s  %a @]@."
       (color "red") default
       (pp_letin ~wloc:wloc) (vs, let_state)
       (color "red") default
       (pp_letin ~wloc:wloc) (vs, let_cont)


and pp_expr ppf =
  function
    | Var vi -> fprintf ppf "%s%s%s" (color "yellow") vi.vname default

    | Array (a, el) -> fprintf ppf "%s%s%s%a" (color "yellow") a.vname default
       (pp_print_list (fun ppf e -> fprintf ppf"[%a]" pp_expr e)) el

    | FunApp (ef, el) -> fprintf ppf "%s (%a)" (psprint80 Cil.dn_exp ef)
       (pp_print_list (fun ppf e -> fprintf ppf"[%a]" pp_expr e)) el

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

    | FRec ((i, g, u), expr) ->
       fprintf ppf "%s(%s;%s;%s)%s { %a }"
         (color "blue")
         (psprint80 Cil.dn_instr i) (psprint80 Cil.dn_exp g)
         (psprint80 Cil.dn_instr u)
         default pp_expr expr

    | FBinop (op, e1, e2) ->
       fprintf ppf "%s %a %a"
         (string_of_symb_binop op)
         pp_expr e1
         pp_expr e2

    | FUnop (op, expr) ->
       fprintf ppf "%s %a"
         (string_of_symb_unop op)
         pp_expr expr

    | FConst c ->
       fprintf ppf "%a"
       pp_constants c

    | FSizeof typ ->
       fprintf ppf "(sizeof %s)"
        (psprint80 Cil.d_type typ)

    | FSizeofE expr ->
       fprintf ppf "(sizeof %a)"
         pp_expr expr

    | FSizeofStr s ->
        fprintf ppf "(sizeof %s)" s

    | FAlignof typ ->
       fprintf ppf "(alignof %s)" (psprint80 Cil.d_type typ)

    | FAlignofE e ->
       fprintf ppf "(alignof %a)" pp_expr e

    | FCastE (t, exp) ->
       fprintf ppf "(cast %s %a)" (psprint80 Cil.d_type t) pp_expr exp

    | FAddrof (lval) ->
       fprintf ppf "(addrof %s)" (psprint80 Cil.d_lval lval)

    | FAddrofLabel _ -> fprintf ppf ""
    | FStartOf _ -> fprintf ppf ""


let printlet ?(wloc=false) letform =
pp_letin ~wloc:wloc std_formatter letform

let eprintlet ?(wloc=false) letform =
pp_letin ~wloc:wloc err_formatter letform

let sprintlet ?(wloc=false) letform =
  pp_letin ~wloc:wloc str_formatter letform ; flush_str_formatter ()
