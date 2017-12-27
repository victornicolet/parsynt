open Cil
open Format
open Findloops
open Utils
open Utils.CilTools
open Utils.PpTools
open SketchTypes
open SPretty
open SError
open Sets

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
  | LetRec of forIGU * letin * letin * location
  | LetCond of expr * letin * letin * letin * location

and expr =
  | Var of varinfo
  | Array of varinfo * (expr list)
  | Container of exp * substitutions
  | FunApp of exp * (expr list)
  | FQuestion of expr * expr * expr
  | FRec of forIGU * expr
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





(** Pretty-printing functions *)
(** A pretty-printing class initialized with all the necessary info *)
class cil2func_printer allvs stv tmps =
  object (self)
    val allvs = VS.union allvs tmps
    val stv = stv

    method pp_letin ?(wloc = false) ppf letin =
      match letin with
      | State expr_map ->
        if IM.is_empty expr_map then
          fprintf ppf "@[{%a}@]"
            VS.pvs stv
        else
          fprintf ppf "@[{%a}@]"
            (ppifmap
               (fun fmt i -> fprintf fmt "%s"
                   (try VS.find_by_id i (VS.union allvs stv)
                    with Not_found ->
                      eprintf "Variable not found@."; raise Not_found).vname)
               self#pp_expr) expr_map

      | Let (vi, expr, letn, id, loc) ->
        fprintf ppf "@[<hov 2>%slet%s@ %s =@ %a@ %sin%s@ %a@]%s"
          (color "red") color_default vi.vname self#pp_expr expr
          (color "red") color_default
          (self#pp_letin ~wloc:wloc) letn
          (if wloc then string_of_loc loc else "")

      | LetRec ((i, g , u), let1, letcont, loc) ->
        fprintf ppf "%sletrec%s (%s,%s,%s) @; %a@]@[%sin%s @[ %a @]%s"
          (color "red") color_default
          (psprint80 Cil.dn_instr i) (psprint80 Cil.dn_exp g)
          (psprint80 Cil.dn_instr u)
          (self#pp_letin ~wloc:wloc) let1
          (color "red") color_default
          (self#pp_letin ~wloc:wloc) letcont
          (if wloc then string_of_loc loc else "")

      | LetCond (exp, letif, letelse, letcont, loc) ->
        fprintf ppf
          "@[<v>@[<hov 4>%sif%s %a %sthen%s@ %a@]@ @[<hov 4>%selse%s %a@]\
           @ @[%sendif%s@]@ %a%s@]"
          (color "red") color_default
          self#pp_expr exp
          (color "red") color_default
          (self#pp_letin ~wloc:wloc) letif
          (color "red") color_default
          (self#pp_letin ~wloc:wloc)  letelse
          (color "red") color_default
          (self#pp_letin ~wloc:wloc) letcont
          (if wloc then string_of_loc loc else "")

    method pp_expr ppf =
      function
      | Var vi -> fprintf ppf "%s%s%s" (color "yellow") vi.vname color_default

      | Array (a, el) -> fprintf ppf "%s%s%s%a" (color "yellow") a.vname color_default
                           (pp_print_list
                              (fun ppf e -> fprintf ppf"[%a]" self#pp_expr e))
                           el

      | FunApp (ef, el) -> fprintf ppf "%s (%a)" (psprint80 Cil.dn_exp ef)
                             (pp_print_list
                                (fun ppf e -> fprintf ppf"[%a]" self#pp_expr e))
                             el

      | Container (e, subs) ->
        if IM.is_empty subs then
          fprintf ppf "%s"
            (psprint80 Cil.dn_exp e)

        else
          fprintf ppf "@[<v 2>%s @[[%a]@]@]@;"
            (psprint80 Cil.dn_exp e)
            (ppifmap
               (fun fmt i ->
                  try fprintf fmt "%s" (VS.find_by_id i allvs).vname
                  with Not_found ->
                    eprintf "Variable id %i not found.@." i;
                    raise Not_found)
               self#pp_expr)
            subs

      | FQuestion (c, a, b) ->
        fprintf ppf "@[<hov 2>(%a@ ?@ %a :@ %a)@]"
          self#pp_expr c self#pp_expr a self#pp_expr b

      | FRec ((i, g, u), expr) ->
        fprintf ppf "%s(%s;%s;%s)%s { %a }"
          (color "blue")
          (psprint80 Cil.dn_instr i) (psprint80 Cil.dn_exp g)
          (psprint80 Cil.dn_instr u)
          color_default self#pp_expr expr

      | FBinop (op, e1, e2) ->
        fprintf ppf "%s %a %a"
          (string_of_symb_binop op)
          self#pp_expr e1
          self#pp_expr e2

      | FUnop (op, expr) ->
        fprintf ppf "%s %a"
          (string_of_symb_unop op)
          self#pp_expr expr

      | FConst c ->
        fprintf ppf "%a"
          (pp_constants ~for_c:false ~for_dafny:false) c

      | FSizeof typ ->
        fprintf ppf "(sizeof %s)"
          (psprint80 Cil.d_type typ)

      | FSizeofE expr ->
        fprintf ppf "(sizeof %a)"
          self#pp_expr expr

      | FSizeofStr s ->
        fprintf ppf "(sizeof %s)" s

      | FAlignof typ ->
        fprintf ppf "(alignof %s)" (psprint80 Cil.d_type typ)

      | FAlignofE e ->
        fprintf ppf "(alignof %a)" self#pp_expr e

      | FCastE (t, exp) ->
        fprintf ppf "(cast %s %a)" (psprint80 Cil.d_type t) self#pp_expr exp

      | FAddrof (lval) ->
        fprintf ppf "(addrof %s)" (psprint80 Cil.d_lval lval)

      | FAddrofLabel _ -> fprintf ppf ""
      | FStartOf _ -> fprintf ppf ""



    method fprintlet ppf ?(wloc=false) letform =
      self#pp_letin ~wloc:wloc ppf letform

    method printlet ?(wloc=false) =
      self#fprintlet std_formatter ~wloc:wloc

    method eprintlet ?(wloc=false) =
      self#fprintlet err_formatter ~wloc:wloc

    method sprintlet ?(wloc=false) letform =
      self#fprintlet str_formatter ~wloc:wloc  letform ; flush_str_formatter ()

    method printsubs subs = self#fprintsubs std_formatter subs

    method fprintsubs ppf subs =
      fprintf ppf "@[<v 2>%a @]"
        (fun fmt subs -> IM.iter
            (fun vid expr -> fprintf ppf "(%i <- %a)@;"
                vid self#pp_expr expr) subs) subs

  end


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
       (fun k v ok -> ok && (VS.has_vid k vs)) emap true)

  | Let (vi, expr, letin, id, loc) -> wf_letin vs letin

  | LetCond (c, let_if, let_else, let_cont, loc) ->
    wf_letin vs let_if && wf_letin vs let_else && wf_letin vs let_cont

  | LetRec ((i, g, u), let_body, let_cont, loc) ->
    wf_letin vs let_body && wf_letin vs let_cont

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

    | _ -> funct letin
  in
  funct applied_in


(** Helpers *)

let empty_state vs = State IM.empty

let container e = Container (e, IM.empty)

let rec used_vars_expr ?(onlyNoOffset = false) (exp : expr) =
  match exp with
  | Container (e, subs) ->
    let in_e = VS.sove e in
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
    let vc = used_vars_expr ~onlyNoOffset:onlyNoOffset c in
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
    VS.unions
      [(used_vars_expr c);
       (used_vars_letin let_if);
       (used_vars_letin let_else);
       (used_vars_letin cont)]

  | LetRec (igu, let_body, cont, loc) ->
    VS.union (used_vars_letin let_body) (used_vars_letin cont)


let rec is_not_identity_substitution vid expr =
  match expr with
  | Var (vi) -> vi.vid != vid
  | Container (e, subs) ->
    ((IM.fold
        (fun k v a -> (is_not_identity_substitution k v) || a)
        subs true)
     ||
     ((VS.max_elt (VS.sove e)).vid != vid))
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

let rec update_subs vse old_subs new_subs =
  (** First apply the new subs in the old subs *)
  let old_subs_updated =
    IM.mapi
      (fun k e ->
         let used_in_e = used_vars_expr e in
         VS.fold
           (fun used_var expr ->
              if IM.mem used_var.vid new_subs
              then apply_subs expr new_subs else expr)
           used_in_e e)
      old_subs
  in
  (** Now add the new substitutions to the old map *)
  IM.fold
    (fun k e upd_subs ->
       if IM.mem k new_subs && VS.has_vid k vse
       then IM.add k (IM.find k new_subs) upd_subs
       else upd_subs) new_subs old_subs_updated




and apply_subs expr subs =
  match expr with
  | Var vi ->
    if !debug then printf "@.Substitute (%i : %s)?@." vi.vid vi.vname;
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
    (** Update the previously existing substitutions *)
    let vse = VS.sove e in
    Container (e, update_subs vse subs' subs)

  | FunApp (ef, el) ->
    FunApp (ef, List.map (fun e -> apply_subs e subs) el)

  | FQuestion (e, e1, e2) ->
    FQuestion (apply_subs e subs, apply_subs e1 subs, apply_subs e2 subs)

  | FRec (igu, e) ->
    FRec (igu, apply_subs e subs)

  | _ -> failwith "Cannot apply substitutions for this expressions."



let bound_state_vars vs lf =
  let rec bound_vars bv =
    function
    | State substitutions ->
      IM.fold
        (fun k _ acc ->
           try
             let vi = VS.find_by_id k vs in
             VS.add vi acc
           with Not_found -> acc) substitutions bv

    | Let (vi, _, cont, _, _) -> bound_vars (VS.add vi bv) cont
    | LetCond (_, l1, l2, l3, _) ->
      let v1 = bound_vars bv l1 in
      let v2 = bound_vars bv l2 in
      bound_vars (VS.union v1 v2) l3
    | LetRec (_, l1, l2, _) ->
      bound_vars (bound_vars bv l1) l2
  in
  bound_vars VS.empty lf


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
      failwith "Substitutions should be empty while bulding let-forms."
  | Let (v, e, olet, id, lc) ->
    Let (v, e, let_add olet new_let, id, lc)

  | LetCond (e, bif, belse, cont, lc) ->
    LetCond (e, bif, belse, let_add cont new_let, lc)

  | LetRec (igu, letform, let_cont, lc) ->
    LetRec (igu, letform, let_add let_cont new_let, lc)

let rec do_il vs il =
  List.fold_left (do_i vs) (empty_state vs) il

and do_i vs let_form =
  let from_lval lv expre loc =
    let vset = VS.sovv ~onlyNoOffset:true lv in
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
  | _ -> failwith "Cil instruction form not supported."

and do_b vs b =
  List.fold_left (do_s vs) (empty_state vs) b.bstmts

and do_s vs let_form s =
  match s.skind with
  | Instr il ->
    let instr_fun = do_il vs il in
    let_add let_form instr_fun

  | If (e, b1, b2, loc) ->
    let ce = Container (e, IM.empty) in
    let block_then = do_b vs b1 in
    let block_else = do_b vs b2 in
    let if_fun = LetCond (ce, block_then, block_else, empty_state vs, loc) in
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

  | Goto (stmt, l) ->
    do_s vs let_form !stmt
  | _ ->
    eprintf "do_s : received unexpected Cil statement : @.@[<hov 4>%s@]@."
      (psprint80 Cil.d_stmt s);
    failwith "Statement unsupported in CPS conversion"



(** Reduction and simplification of expressions and lets *)
let let_add2 old_let new_let vs =
  let rec let_add2_aux old_let new_let =
    match old_let with
    | State subs ->
      if IM.is_empty subs then
        new_let
      else
        let stmt_id = gen_id () in
        let def_loc = {line = 0; file = "__NONE"; byte = 0} in
        let let_head =
          IM.fold
            (fun i e let_head ->
               (Let (VS.find_by_id i vs, e, let_head, stmt_id, def_loc)))
            subs
            (State IM.empty)
        in
        let_add2_aux let_head new_let

    | Let (v, e, olet, id, lc) ->
      Let (v, e, let_add2_aux olet new_let, id, lc)

    | LetCond (e, bif, belse, cont, lc) ->
      LetCond (e, bif, belse, let_add2_aux cont new_let, lc)

    | LetRec (igu, letform, let_cont, lc) ->
      LetRec (igu, letform, let_add2_aux let_cont new_let, lc)
  in
  let_add2_aux old_let new_let

(** Try merging old and new substitutions. The new subtitutions correspond
    to a statement summary (ex : an if statement is a susbtituation containing
    ternary expressions). IF the substitutions are disjoint, meaning that no
    variable is used in new subs and susbtituted in old subs, we merge.
    Otherwise we return the new substitutions and a state representing the old
    substitutions (this will need let-bindings)
*)
let merge_substs vs old_subs new_subs : bool * expr IM.t * letin option =
  let used_in_new_subs =
    (IM.fold (fun k v b -> VS.union b (used_vars_expr v))
       new_subs VS.empty)
  in
  if
    (* Check if the variables that are assigned in old_subs
       are used in new_subs *)
    (IM.is_disjoint ~non_empty:is_not_identity_substitution
       old_subs new_subs) &&
    not (IM.exists (fun k v -> VS.has_vid k used_in_new_subs)
           old_subs)
  then
    true, (IM.add_all old_subs new_subs), None
  else true, new_subs, Some (State old_subs)

(**
   Merge two conditions, if each branch is irreducible (already
   reduced to a single state) then transform each substitution
   expression into a FQuestion (an expression instead of a lambda)
   @param vs The state variables
   @param c The conditional expression
   @param let_if the if branch of the LetCond
   @param let_else the else branch of the LetCond
   @param pre_substs the substitutions before the LetCond
   @return A triple containing :
   - a boolean set to true if the merge succeeds
   - the substituions after the LetCond
   - the expression replacing the LetCond
*)

let rec  merge_cond vs c let_if let_else pre_substs =
  match let_if, let_else with

  | State subs_if , State subs_else ->
    let new_subs =
      IM.merge
        (fun vid if_expr_o else_expr_o ->
           let cur_var = Var (VS.find_by_id vid vs) in
           let mod_cond = c in
           match if_expr_o, else_expr_o with
           | Some if_expr, Some else_expr ->
             Some (FQuestion (mod_cond, if_expr, else_expr))

           | Some if_expr, None ->
             Some
               (FQuestion
                  (mod_cond, if_expr, cur_var))

           | None, Some else_expr->
             Some
               (FQuestion
                  (mod_cond, cur_var, else_expr))
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

and convert_loop vs tmps let_body igu let_cont loc =
  match let_body with
  | State subs ->
    let subs' = remove_identity_subs subs in
    if (IM.cardinal subs') = 1
    then
      let vid, expr = IM.max_binding subs' in
      let rec_expr = FRec (igu, expr) in
      let id = gen_id () in
      add_uses id (used_vars_expr rec_expr);
      true,  Let (VS.find_by_id vid vs, rec_expr, let_cont, id, loc)
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

and red vs tmps let_form substs =
  match let_form with
  | State emap ->
    let id_list = VS.vids_of_vs vs in
    let final_state_exprs =
      IM.filter (fun k v -> List.mem k id_list) substs
    in
    State final_state_exprs

  | Let (vi, expr, cont, id, _) ->
    let nexpr = apply_subs expr substs in
    let nsubs = IM.add vi.vid nexpr substs in
    red vs tmps cont nsubs

  | LetRec (igu, body, cont, loc) ->
    let redd_body = reduce vs tmps body in
    let redd_cont = reduce vs tmps cont in
    let converted, conversion =
      convert_loop vs tmps redd_body igu redd_cont loc in
    if converted then
      conversion
    else
      LetRec (igu, redd_body, reduce vs tmps cont, loc)

  | LetCond (e, bif, belse, cont, loc) ->
    let ce = e  in
    let red_if = reduce vs tmps bif in
    let red_else = reduce vs tmps  belse in
    let merged, nsubs, olde_o = merge_cond vs ce red_if red_else substs in
    if merged
    then
      match olde_o with
      | Some olde -> let_add2 olde (red vs tmps cont nsubs) vs
      | None -> red vs tmps cont nsubs
    else
      LetCond (ce,
               red vs tmps bif substs,
               red vs tmps belse substs,
               red vs tmps cont substs, loc)

and clean vs let_form =
  match let_form with
  | State emap ->
    State (IM.filter (fun k e -> VS.has_vid k vs) emap)

  | Let (v, e, c, id, loc) ->
    if VS.mem v vs then Let(v, e, clean vs c, id, loc) else
      failwith "Func2cil : Non-state variable bound in let form."

  | LetCond (ce, lif, lelse, lcont, loc) ->
    LetCond (ce, clean vs lif, clean vs lelse, clean vs lcont, loc)

  | LetRec (figu, lbody, lcont, loc) ->
    LetRec (figu, clean vs lbody, clean vs lcont, loc)

and reduce vs tmps let_form =
  let reduced_form = red vs tmps let_form IM.empty in
  clean vs reduced_form

(** We want to write only in state variables. This step eliminates
    bindings to temporary variables by replacing their expression in
    the different let-forms *)


let merge_cond_subst allvs vs c subs_if subs_else =
  (* if_in_else : substitutions in if when there is a substitution in else
     else_in_if : sub in else when there exists a sub in if *)
  let if_in_else, else_in_if, if_only, else_only =
    IM.disjoint_sets subs_if subs_else in
  (* Join the expressions for variables in the intersection *)
  let add_iden_sub vid subs =
    try
      IM.add vid (Var (VS.find_by_id vid allvs)) subs
    with Not_found ->
      (eprintf "Failed to build identity substitution in \
                branch for variable id %i@." vid;
       raise Not_found)
  in
  let if_in_else, else_in_if =
    if IM.cardinal if_only > 0|| IM.cardinal else_only > 0 then

      (IM.fold
         (fun vid e iie -> add_iden_sub vid iie)
         else_only if_in_else,

       IM.fold
         (fun vid e eii -> add_iden_sub vid eii)
         if_only else_in_if)

    else
      if_in_else, else_in_if
  in
  let ifmap, elsemap =
    IM.add_all if_in_else if_only,
    IM.add_all else_in_if else_only
  in
  IM.mapi
    (fun k v ->
       let v' = IM.find k elsemap in
       FQuestion (c, v, v')) ifmap


(**
   vid -> n_expr is a new substitution for subs. Update all the substitutions
   first, by performing the substituion vid -> n_expr in each of the
   substitutions, and then add the substitution to the set.
*)
let add_sub vid n_expr subs =
  IM.add vid n_expr
    (IM.map
       (fun e -> apply_subs e (IM.singleton vid n_expr)) subs)

(**
   Eliminate CIL's introduced temporaries. A temporary is a variable that is
   written but is not in the state (it has been filtered out of the state).
   The elimination is performed on the non-reduced form by keeping a mapping of
   the substitutions f temporaries to expressions while descending in the
   AST of the function.
*)
let eliminate_temporaries allvs vs tmps let_form =
  let debug_counter = ref 0 in
  let cfprinter = new cil2func_printer allvs vs tmps in
  let rec elim_let_aux let_form subs =
    if !debug then
      begin
        printf "@.------STEP %i-------@.\
               Substitutions: %a@.@[<v 4> Function:@ %a@]@." !debug_counter
        cfprinter#fprintsubs subs
        (cfprinter#fprintlet ~wloc:false) let_form;
        incr debug_counter;
      end;
    match let_form with
    | Let (vi, expr, letcont, id, loc) ->
      let n_expr = apply_subs expr subs in
      begin
        if VS.mem vi vs then
          (* vi is not a temporary, but a state variable. *)
          let new_cont, fsubs = elim_let_aux letcont subs in
          (* Eliminate the variable assigned from the current subs. *)
          Let (vi, n_expr, new_cont , id, loc), fsubs

        else
          (* vi is a temporary variable. *)
          let new_subs = add_sub vi.vid n_expr subs in
          elim_let_aux letcont new_subs
      end

    | LetRec ( figu, let1, let2, loc) ->
      let nlet1, subs =  elim_let_aux let1 subs in
      let nlet2, subs =  elim_let_aux let1 subs in
      LetRec (figu, nlet1, nlet2, loc), subs

    | LetCond (c, lif, lelse, letcont, loc) ->
      let c' = elim_expr vs subs c in
      let nlif, subs_if = elim_let_aux lif subs in
      let nlelse, subs_else = elim_let_aux lelse subs in
      let merged_subs = merge_cond_subst allvs vs c' subs_if subs_else in
      let nlcont, nsubs = elim_let_aux letcont merged_subs in
      let bv_if = bound_state_vars vs nlif in
      let bv_else = bound_state_vars vs nlelse in
      if VS.is_empty bv_if && VS.is_empty bv_else then
        nlcont, nsubs
      else
        LetCond (c', nlif, nlelse, nlcont, loc), nsubs

    | State sk ->
      State (IM.map (elim_expr vs subs) sk), subs

  and elim_expr vs subs expr =
    apply_subs expr subs
  in
  if wf_letin vs let_form then
    fst (elim_let_aux let_form IM.empty)
  else
    failwith "Ill formed let-bindings"

(**
   MAIN ENTRY POINT
*)
let init map_loops = loops := map_loops;;

let cil2func allvs statevs tmps block (i,g,u) =
  (**
      We need the other loops in case of nested loops to avoid
      recomputing the for statement in the inner loops.
  *)
  try
    begin
      if IM.cardinal !loops = 0 then
        failwith "You forgot to initialize the set of loops in Cil2Func ?";
      if !debug then eprintf "-- Cil --> Functional --";
      let printer = new cil2func_printer statevs statevs tmps in
      let let_expression_0 = (do_b statevs block) in
      let let_expression =
        eliminate_temporaries allvs statevs tmps let_expression_0
      in
      let index = index_of_igu (i,g,u) in
      let init_f = do_il statevs [i] in
      let update_f = do_il statevs [u] in
      let guard_e = Container (g, IM.empty) in
      let func, figu =
        reduce statevs tmps let_expression, (index, (init_f, guard_e, update_f))
      in
      if !debug then
        printf "@.CIL --> FUNCTION transformation result:@.\
                - Before reduction:@.%a@.\
                - Eliminate temporaries:@.%a@.\
                - After reduction:@.%a@."
          (printer#pp_letin ~wloc:false) let_expression_0
          (printer#pp_letin ~wloc:false) let_expression
          (printer#pp_letin ~wloc:false) func;

      func, figu
    end
  with Failure s -> fail_functional_conversion s
