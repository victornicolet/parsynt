(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
  *)

open Beta
open Cil
open Format
open Loops
open Utils
open Utils.CilTools
open Utils.PpTools
open FuncTypes
open FPretty
open FError
open Sets
open Loops

(**
   Implementation of a simple CPS conversion from the
   Cil program to a let-forms program with conditonals
   and loops.
   The loops can be translated in a straightforawrd
   manner to a recursive function.
 *)


let debug = ref false
(** The loops in the files *)
let global_loops = IH.create 10

let uses = ref (IH.create 10)
let add_uses id vs = IH.add !uses id vs

let __letin_index = ref 0
let gen_letin_id () = incr __letin_index; !__letin_index

type lhs =
  | LhVar of varinfo
  | LhElem of lhs * expr
  | LhTuple of VS.t

and letin =
  | State of (expr IM.t)
  | Let of lhs * expr * letin * int * location
  | LetCond of expr * letin * letin * letin * location

and expr =
  | Var of varinfo
  | Array of varinfo * (expr list)
  | Container of exp * substitutions
  | FunApp of exp * (expr list)
  | FQuestion of expr * expr * expr
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


let rec array_of_elem elem_lhs =
  match elem_lhs with
  | LhVar vi ->
     if VariableAnalysis.is_pointer vi then
       Some vi
     else None
  | LhElem (a, _) -> array_of_elem a
  | _ -> None


(** Pretty-printing functions *)
(** A pretty-printing class initialized with all the necessary info *)
class cil2func_printer variables =
object (self)
  val allvs = VS.union variables.all_vars variables.tmp_vars
  val stv = variables.state_vars

  method pp_lhs ppf lhs =
    match lhs with
    | LhVar vi -> fprintf ppf "%s" vi.vname
    | LhElem (a, ofs) -> fprintf ppf "%a[%a]" self#pp_lhs a self#pp_expr ofs
    | LhTuple vs ->
       pp_print_list ~pp_sep:(fun fmt () -> fprintf ppf ", ")
         (fun fmt vi -> fprintf ppf "%s" vi.Cil.vname)
         ppf
         (VS.elements vs)

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
       fprintf ppf "@[<hov 2>%slet%s@ %a =@ %a@ %sin%s@ %a@]%s"
         (color "red") color_default
         self#pp_lhs vi self#pp_expr expr
         (color "red") color_default
         (self#pp_letin ~wloc:wloc) letn
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
                              ~pp_sep:(fun fmt () -> fprintf fmt ", ")
                              (fun ppf e -> fprintf ppf"%a" self#pp_expr e))
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

    | _ -> funct letin
  in
  funct applied_in


(** Helpers *)

let empty_state () = State IM.empty

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
    | FUnop (_, e) ->
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

  | _ -> failwith "Cannot apply substitutions for this expressions."


(* v has been substituted with e in expr. Revert this. *)
let rec revert_sub e v expr =
  match expr with
  | expr when expr = e -> Var v
  | FBinop(op, e1, e2) -> FBinop (op, revert_sub e v e1, revert_sub e v e2)
  | FUnop(op, e1) -> FUnop (op, revert_sub e v e1)
  | Array (v, i) -> Array (v, List.map (revert_sub e v) i)
  | Container (ce, subs) ->
    Container (ce, IntegerMap.map (fun e' -> if e = e' then Var v else e') subs)
  | FQuestion (c, t, f) -> FQuestion (revert_sub e v c,
                                      revert_sub e v t,
                                      revert_sub e v f)
  | FunApp (ce, el) -> FunApp (ce, List.map (revert_sub e v) el)
  | _ -> expr


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

    | Let (lhv, _, cont, _, _) ->
       (match lhv with
        | LhVar vi ->
           bound_vars (VS.add vi bv) cont
        | LhElem (a, ofs) ->
           bound_vars (match array_of_elem a with
            | Some vi -> (VS.add vi bv)
            | None -> bv) cont
        | LhTuple vil ->
           bound_vars (VS.union vil bv) cont)

    | LetCond (_, l1, l2, l3, _) ->
       let v1 = bound_vars bv l1 in
       let v2 = bound_vars bv l2 in
       bound_vars (VS.union v1 v2) l3
  in
  bound_vars VS.empty lf


(**
   Prepend a set of bindings to a let form. The input is a list of
   bindings considered to be parallel assignments.
*)
let rec let_prepend binding_list cont =
  let update_tl e v bl = List.map (fun (v', e') -> (v', revert_sub e v e')) bl in
  let rec build_header bl =
    match bl with
    | [] -> cont
    | (v, e) :: tl ->
      let ntl = update_tl e v tl in
      Let (LhVar v, e, build_header ntl, -1, defloc)
  in
  build_header binding_list

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


let rec do_lval vs lval e let_form loc =
  (* build_elemt builds array accesses with the correct order
     for the offsets.
  *)
  let rec build_elemt x offsets =
    List.fold_left
      (fun elemt offset -> LhElem(elemt, container offset))
      (LhVar x) offsets
  in
  (* lhs : left hand side of an assignment. Builds the let-bindings *)
  let do_lhs (lval : Cil.lval) =
    match lval with
    | Var v, NoOffset -> LhVar v
    | h , o ->
       let mvi, ofs = VariableAnalysis.analyze_host h in
       let ofs2 = VariableAnalysis.analyze_offset o in
       (match mvi with
       | Some x ->
          (build_elemt x (ofs@ofs2))
       | None ->
          failhere __FILE__ "do_lval" "Bad left hand side in assignment.")
  in
  let id = gen_letin_id () in
  add_uses id (used_vars_expr e);
  let_add let_form (Let (do_lhs lval, e, (empty_state ()), id, loc))

and do_il vs il =
  List.fold_left (do_i vs) (empty_state ()) il

and do_i vs let_form =
  function
  | Set (lv, exp, loc) ->
     do_lval vs lv (container exp) let_form loc

  | Call (lvo, ef, e_argli, loc) ->
     begin
       match lvo with
       | Some lv ->
          let func_app =  FunApp (ef, (List.map container e_argli)) in
          do_lval vs lv func_app let_form loc
       | None ->
          (* Side effects not supported but check if it is an inner loop call *)
          begin
            match ef with
            | Lval (hfun, ofun) when ofun = NoOffset ->
               let fname, fvi =
                 match hfun with
                 | Var vi -> vi.vname, vi
                 | _ -> failwith  "do_i : unexpected function call"
               in
               (* Inner loop specific. *)
               if Conf.is_inner_loop_func_name fname then
                 (* Replace by a binding to state variables of the inner loop *)
                 let func_app = FunApp (ef, List.map container e_argli) in
                 do_lval vs (hfun, ofun) func_app let_form loc
               else
                 failwith "do_i : side effects not suppoerted."
            | _ -> failwith "do_i : side effects no supported."
          end
     end
  | _ -> failwith "Cil instruction form not supported."

and do_b vs b =
  List.fold_left (do_s vs) (empty_state ()) b.bstmts

and do_s vs let_form s =
  match s.skind with
  | Instr il ->
     begin
       try
         (* Case : the instruction list only contains the call to the inner loop *)
         if List.length il != 1 then raise Not_found;
         let innerloop = IH.find global_loops s.sid in
         let stv = innerloop.lvariables.state_vars in
         let uvs = innerloop.lvariables.used_vars in
         let fvi, floc =
           match List.nth il 0 with
           | Call (_, ef, args,loc) ->
              (match ef with
               | Lval (Var vi, NoOffset) -> vi
               | _ -> failwith "do_s : failed to get an inner loop function."),
              loc
           | _ -> failwith "do_s : failed to get an inner loop function"
         in
         let args = List.map (fun vi -> Var vi) (VS.varlist uvs) in
         let fapp = FunApp (Lval (Var fvi, NoOffset), args) in
         let innerloop_call =
           Let(LhTuple stv, fapp, empty_state (), 0, locUnknown)
         in
         let_add let_form innerloop_call
       with Not_found ->
         let instr_fun = do_il vs il in
         let_add let_form instr_fun
     end
  | If (e, b1, b2, ploc) ->
     let ce = Container (e, IM.empty) in
     let block_then = do_b vs b1 in
     let block_else = do_b vs b2 in
     let if_fun = LetCond (ce, block_then, block_else, empty_state (), ploc) in
     let_add let_form if_fun

  | Loop (b, loc,_,_) ->
     failhere __FILE__ "do_s"
       "Loops not supported: should be abstracted as a function."
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
         let stmt_id = gen_letin_id () in
         let def_loc = {line = 0; file = "__NONE"; byte = 0} in
         let let_head =
           IM.fold
             (fun i e let_head ->
               (Let (LhVar (VS.find_by_id i vs),
                     e, let_head, stmt_id, def_loc)))
             subs
             (State IM.empty)
         in
         let_add2_aux let_head new_let

    | Let (v, e, olet, id, lc) ->
       Let (v, e, let_add2_aux olet new_let, id, lc)

    | LetCond (e, bif, belse, cont, lc) ->
       LetCond (e, bif, belse, let_add2_aux cont new_let, lc)
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
       (* TODO: removed FRec type but have to fix this *)
       let rec_expr = FunApp (igu, [expr]) in
       let id = gen_letin_id () in
       add_uses id (used_vars_expr rec_expr);
       true,  Let (LhVar (VS.find_by_id vid vs), rec_expr, let_cont, id, loc)
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

  | Let (lhv, expr, cont, id, loc) ->
     (* Don't reduce if expr is a loop function call *)
     begin
     match expr with
     | FunApp (Lval (Var f, NoOffset), args)
          when Conf.is_inner_loop_func_name f.vname ->
        (match lhv with
         | LhVar vi ->
            let nexpr = apply_subs expr substs in
            let nsubs = IM.add vi.vid (Var vi) substs in
            Let(lhv, nexpr, red vs tmps cont nsubs, id, loc)

         | LhElem (lhs, ofs) ->
            let nexpr = apply_subs expr substs in
            Let(lhv, nexpr, red vs tmps cont substs, id, loc)

         | LhTuple vil ->
            let nexpr = apply_subs expr substs in
            let nsubs =
              VS.fold
                (fun vi nsubs -> IM.add vi.vid (Var vi) nsubs)
                vil substs
            in
            Let(lhv, nexpr, red vs tmps cont nsubs, id, loc))

     | _ ->
        match lhv with
        | LhVar vi ->
           let nexpr = apply_subs expr substs in
           let nsubs = IM.add vi.vid nexpr substs in
           red vs tmps cont nsubs

        (* Do not keep reducing for arrays, and don't apply the
           reduction: reinstall the bindings for the variables
           used in the bound expression above.
        *)
        | LhElem (a, i) ->
          let usedvs = used_vars_expr expr in
          let nsubs, reinstall_bindings =
            VS.fold
              (fun v (nsubs, bindings) ->
                 try
                   let e = IM.find v.vid nsubs in
                   (IM.remove v.vid nsubs, (v, e)::bindings)
                 with Not_found ->
                   (nsubs, bindings))
              usedvs (substs, [])
          in
          let_prepend
            reinstall_bindings
            (Let(lhv, expr, red vs tmps cont nsubs, id, loc))

        | LhTuple vil ->
           let nexpr = apply_subs expr substs in
           let nsubs =
             VS.fold
               (fun vi nsubs -> IM.add vi.vid nexpr nsubs)
               vil substs
           in
           red vs tmps cont nsubs
     end

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
     let lhs =
       match v with LhVar vi -> VS.singleton vi
                  | LhElem (a,_) ->
                     (match array_of_elem a with
                      | Some vi -> VS.singleton vi
                      | None -> VS.empty)
                  | LhTuple vil -> vil
     in
     if not (VS.is_empty (VS.diff vs lhs))
     then Let(v, e, clean vs c, id, loc)
     else
       (VS.ppvs (VS.diff lhs vs);
       failwith "Cil2func : Non-state variable bound in let form.")

  | LetCond (ce, lif, lelse, lcont, loc) ->
     LetCond (ce, clean vs lif, clean vs lelse, clean vs lcont, loc)


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
let eliminate_temporaries variables let_form =
  let vs, allvs, tmp =
    variables.state_vars, variables.all_vars, variables.tmp_vars
  in
  let debug_counter = ref 0 in
  let cfprinter = new cil2func_printer variables in
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
    | Let (lhv, expr, letcont, id, loc) ->
       begin
         match lhv with
         | LhVar vi ->
            let n_expr = apply_subs expr subs in
            if VS.mem vi vs then
              (* vi is not a temporary, but a state variable. *)
              let new_cont, fsubs = elim_let_aux letcont subs in
              (* Eliminate the variable assigned from the current subs. *)
              Let (LhVar vi, n_expr, new_cont , id, loc), fsubs

            else
              (* vi is a temporary variable. *)
              let new_subs = add_sub vi.vid n_expr subs in
              elim_let_aux letcont new_subs

         | LhElem _ | LhTuple _ ->
            let n_expr = apply_subs expr subs in
            (* No temporaries are tuples or arrays *)
            let new_cont, fsubs = elim_let_aux letcont subs in
            Let(lhv, n_expr, new_cont, id, loc), fsubs
       end


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


let unwrap_consts =
  IM.map
    (fun cexp ->
      match cexp with
      | Const c -> c
      | _ ->  failwith "Cil2Func.ml : unwrap consts : not a const")
(**
   MAIN ENTRY POINT
 *)
let init map_loops =
  let rec add_loop_to_glob id lp =
    IH.add global_loops id lp;
    List.iter (fun ilp -> add_loop_to_glob ilp.lid ilp) lp.inner_loops
  in
  IM.iter add_loop_to_glob map_loops



let cil2func (variables : Loops.variables) block (i,g,u) =
  (**
Prepare the environment for the conversion. Inner loops are functions
inside the parent loop.

 We need the other loops in case of nested loops to avoid
      recomputing the for statement in the inner loops.
   *)
  try
    begin
      if IH.length global_loops = 0 then
        failwith "You forgot to initialize the set of loops in Cil2Func ?";
      if !debug then printf "-- Cil --> Functional --";
      let statevs = variables.state_vars in
      let tmps = variables.tmp_vars in
      let printer = new cil2func_printer variables in
      let let_expression_0 = (do_b statevs block) in
      let let_expression =
        eliminate_temporaries variables let_expression_0
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

      func, Some figu
    end
  with Failure s -> fail_functional_conversion s
