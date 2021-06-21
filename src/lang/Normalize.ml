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

open AcTerm
open Base
open ResourceModel
open Term
open TermUtils
open Typ
open Unfold
open Utils

type cond = term list

type mcnf = (cond * term) list

type mcnf_extended = (cond * term * term Array.t) list

type normalized_unfolding = {
  u : unfolding IM.t;
  from_symb_mcnf : mcnf_extended IM.t;
  from_init_mcnf : mcnf IM.t;
}

type local_context = Binop.t * term

type collect_result = { context_tree : term; aux_exprs : term Map.M(String).t }
(** Collect result: represents an expression (the context tree) where
    all the expressions that need to be collected for paralellelization
    have been replaced in the tree by a variable and the variable name
    maps to the expression in aux_exprs.
*)

let is_cr_aux (t : term) (cr : collect_result) =
  match t.texpr with EVar (Var v) -> Option.is_some (Map.find cr.aux_exprs v.vname) | _ -> false

let has_cr_aux (t : term) (cr : collect_result) =
  let init = false in
  let join = ( || ) in
  let case _ t = if is_cr_aux t cr then Some true else None in
  Transform.recurse { init; join; case } t

let skeletize (cr : collect_result) : term -> term =
  let tf _ t =
    let ttyp = match type_of t with Ok x -> x | Error _ -> TTop in
    if is_cr_aux t cr then Some (mk_hole ~attrs:t.tattrs (ttyp, 0))
    else if not (has_cr_aux t cr) then Some (mk_hole ~attrs:t.tattrs (ttyp, 1))
    else None
  in
  Transform.transform tf

(* ============================================================================== *)
(* Normalization rules. *)
(* Associativity / commutativity *)
let ac_opt_rule (fcost : term -> term -> int) : (term -> term) -> term -> term =
 fun _ e -> rebuild_tree_AC fcost (to_ac e)

(* RULES *)
let distrib_rule (f : term -> term) (t : term) =
  match t.texpr with
  | EBin (op1, t1, t2) -> (
      match (t1.texpr, t2.texpr) with
      | EBin (op2, a, b), _ when distributes op1 op2 ->
          mk_bin (f (mk_bin a op1 t2)) op2 (f (mk_bin b op1 t2))
      | _, EBin (op2, a, b) when distributes op1 op2 ->
          mk_bin (f (mk_bin t1 op1 a)) op2 (f (mk_bin t1 op1 b))
      | _ -> t)
  | _ -> t

let unary_down_rule (f : term -> term) (t : term) =
  match t.texpr with
  | EUn (Neg, x) -> (
      match x.texpr with
      | EBin (Plus, a, b) -> mk_add (f (mk_opp a)) (f (mk_opp b))
      | EBin (Max, a, b) -> mk_min (f (mk_opp a)) (f (mk_opp b))
      | EBin (Min, a, b) -> mk_max (f (mk_opp a)) (f (mk_opp b))
      | EBin (Times, a, b) -> mk_mul (f (mk_opp a)) b
      | EBin (Minus, a, b) -> mk_sub b a
      | EUn (Neg, a) -> a
      | _ -> t)
  | EUn (Not, x) -> (
      match x.texpr with
      | EBin (And, a, b) -> mk_or (f (mk_not a)) (f (mk_not b))
      | EBin (Or, a, b) -> mk_and (f (mk_not a)) (f (mk_not b))
      | EUn (Not, a) -> a
      | _ -> t)
  | _ -> t

let factor_rule (f : term -> term) (t : term) =
  match t.texpr with
  | EBin (op2, t1, t2) -> (
      match (t1.texpr, t2.texpr) with
      | EBin (op1, a, c), EBin (op1', b, c')
        when Binop.(op1 = op1') && distributes op1 op2 && ACES.(c = c') ->
          mk_bin (f (mk_bin a op2 b)) op1 c
      | EBin (op1, c, a), EBin (op1', c', b)
        when Binop.(op1 = op1') && distributes op1 op2 && ACES.(c = c') ->
          mk_bin c op1 (f (mk_bin a op2 b))
      | _, EBin (op1, c', b) when has_ident op1 && distributes op1 op2 && ACES.(t1 = c') ->
          let e0 = mk_term (Option.value_exn (ident_elt op1)) in
          mk_bin t1 op1 (f (mk_bin e0 op2 b))
      | EBin (op1, c', b), _ when has_ident op1 && distributes op1 op2 && ACES.(t2 = c') ->
          let e0 = mk_term (Option.value_exn (ident_elt op1)) in
          mk_bin t2 op1 (f (mk_bin e0 op2 b))
      (* (a1 or b1) and ((a2 or b2) and t3) --> (a1 or (b1 and b2)) and t3 *)
      | EBin (op1, a1, b1), EBin (op2', { texpr = EBin (op1', a2, b2); _ }, t3)
        when Binop.(op2 = op2') && Binop.(op1 = op1') && distributes op2 op1 ->
          if ACES.(a1 = a2) then mk_bin (mk_bin (f a1) op1 (f (mk_bin b1 op2 b2))) op2 (f t3)
          else if ACES.(b1 = b2) then mk_bin (mk_bin (f b1) op1 (f (mk_bin a1 op2 a2))) op2 (f t3)
          else t
      | _ -> t)
  | _ -> t

let compar_max_rule (f : term -> term) (t : term) =
  match t.texpr with
  | EBin (o1, t1, t2) -> (
      match (t1.texpr, t2.texpr) with
      | EBin (Max, a, b), _ when Binop.(o1 = Gt || o1 = Ge) ->
          let e1 = f (mk_bin a o1 t2) in
          let e2 = f (mk_bin b o1 t2) in
          mk_or e1 e2
      | _, EBin (Max, a, b) when Binop.(o1 = Gt || o1 = Ge) ->
          let e1 = f (mk_bin t1 o1 a) in
          let e2 = f (mk_bin t1 o1 b) in
          mk_and e1 e2
      | EBin (Max, a, b), _ when Binop.(o1 = Lt || o1 = Le) ->
          let e1 = f (mk_bin a o1 t2) in
          let e2 = f (mk_bin b o1 t2) in
          mk_and e1 e2
      | _, EBin (Max, a, b) when Binop.(o1 = Lt || o1 = Le) ->
          let e1 = f (mk_bin t1 o1 a) in
          let e2 = f (mk_bin t1 o1 b) in
          mk_or e1 e2
      (* min(a,b) > c -> a > c and b > c *)
      | EBin (Min, a, b), _ when Binop.(o1 = Gt || o1 = Ge) ->
          let e1 = f (mk_bin a o1 t2) in
          let e2 = f (mk_bin b o1 t2) in
          mk_and e1 e2
      (* c > min(a,b) -> a > c or b > c *)
      | _, EBin (Min, a, b) when Binop.(o1 = Gt || o1 = Ge) ->
          let e1 = f (mk_bin t1 o1 a) in
          let e2 = f (mk_bin t1 o1 b) in
          mk_or e1 e2
      (* min(a,b) < c -> a < c or b < c *)
      | EBin (Min, a, b), _ when Binop.(o1 = Lt || o1 = Le) ->
          let e1 = f (mk_bin a o1 t2) in
          let e2 = f (mk_bin b o1 t2) in
          mk_or e1 e2
      (* c < min(a,b) -> c< a and c < b *)
      | _, EBin (Min, a, b) when Binop.(o1 = Lt || o1 = Le) ->
          let e1 = f (mk_bin t1 o1 a) in
          let e2 = f (mk_bin t1 o1 b) in
          mk_or e1 e2
      | _ -> t)
  | _ -> t

let identity_rule (_ : term -> term) (t : term) = t

let cond_norm_rule (f : term -> term) (t : term) =
  match t.texpr with
  | EBin (o1, t1, t2) -> (
      match (t1.texpr, t2.texpr) with
      | EIte (c, e1, e2), EIte (c', e1', e2') when Terms.(c = c') ->
          let e11 = f (mk_bin e1 o1 e1') in
          let e22 = f (mk_bin e2 o1 e2') in
          mk_ite (f c) e11 e22
      | EIte (c, e1, e2), EIte (c', e1', e2') when Terms.(mk_not c = c') ->
          let e12 = f (mk_bin e1 o1 e2') in
          let e21 = f (mk_bin e2 o1 e1') in
          mk_ite (f c) e12 e21
      | EIte (c, e1, e2), EIte (c', e1', e2') when Terms.(c = mk_not c') ->
          let e12 = f (mk_bin e1 o1 e2') in
          let e21 = f (mk_bin e2 o1 e1') in
          mk_ite (f c) e21 e12
      | EIte (c, e1, e2), EIte (c', e1', e2') when not Terms.(c = c') ->
          let e11 = f (mk_bin e1 o1 e1') in
          let e12 = f (mk_bin e1 o1 e2') in
          let e21 = f (mk_bin e2 o1 e1') in
          let e22 = f (mk_bin e2 o1 e2') in
          let c = f c in
          let c' = f c' in
          mk_ite c (mk_ite c' e11 e12) (mk_ite c' e21 e22)
      | _, EIte (c, e1', e2') ->
          let ee1 = f (mk_bin t1 o1 e1') in
          let ee2 = f (mk_bin t1 o1 e2') in
          mk_ite (f c) ee1 ee2
      | EIte (c, e1, e2), _ ->
          let e1e = f (mk_bin e1 o1 t2) in
          let e2e = f (mk_bin e2 o1 t2) in
          mk_ite (f c) e1e e2e
      | _ -> t)
  | EUn (u, t1) -> (
      match t1.texpr with
      | EIte (c, e1, e2) ->
          let e1' = f (mk_un u e1) in
          let e2' = f (mk_un u e2) in
          mk_ite c e1' e2'
      | _ -> t)
  (* | EIte(cond, et, ef) when is_bool t ->
      mk_or (mk_and (f cond) (f et)) (f ef) *)
  | _ -> t

let cond_fact_rule (f : term -> term) (t : term) =
  match t.texpr with
  | EIte (cnd, t1, t2) -> (
      match (t1.texpr, t2.texpr) with
      | EBin (o, a, c), EBin (o', b, c') when Binop.(o = o') && Terms.(c = c') ->
          let ca = f (mk_ite cnd a b) in
          mk_bin ca o c
      | EBin (o, c, a), EBin (o', c', b) when Binop.(o = o') && Terms.(c = c') ->
          let ca = f (mk_ite cnd a b) in
          mk_bin c o ca
      | _ -> t)
  | _ -> t

let is_cond_normal (e : term) =
  let rec check e =
    Transform.recurse
      {
        init = true;
        join = ( && );
        case =
          (fun _ t ->
            match t.texpr with EBin _ | EUn _ | EList _ -> Some (not (check_anti t)) | _ -> None);
      }
      e
  and check_anti e =
    Transform.recurse
      {
        init = false;
        case = (fun _ t -> match t.texpr with EIte _ -> Some true | _ -> None);
        join = (fun a b -> a || b);
      }
      e
  in
  match e.texpr with EIte _ -> check e | _ -> false

let apply_to_noncond (f : term -> term) : term -> term =
  let sel _ e = match e.texpr with EIte _ -> Some (f e) | _ -> None in
  Transform.transform sel

let cond_normal_rules (t : term) = Transform.apply_bottom_up_rule cond_norm_rule t

let minimize_cost (costly : resource list) (term : term) : term =
  let fcost e1 e2 = compare_dc_cost (dc_cost_of_term costly e1) (dc_cost_of_term costly e2) in
  let rules e =
    rebuild_tree_AC fcost
    @@ factorize (terms_of_resources costly)
    @@ (Transform.apply_bottom_up_rules
          [
            distrib_rule;
            factor_rule;
            cond_norm_rule;
            cond_fact_rule;
            compar_max_rule;
            unary_down_rule;
            ac_opt_rule fcost;
            identity_rule;
          ]
          fcost)
         e
  in
  let rules e = simplify_easy @@ rules e in
  let term = to_list_normal_form term in
  match term.texpr with
  | EIte _ -> if is_cond_normal term then apply_to_noncond rules term else rules term
  | _ -> rules term

(* Main entry points. *)
let normalize ?(costly : resource list = []) (t : term) =
  if List.is_empty costly then cond_normal_rules t
  else
    let t' = cond_normal_rules t in
    minimize_cost costly t'

let norm_comparison t =
  let rule t =
    match t.texpr with
    | EBin (Gt, t1, t2) -> mk_bin t2 Lt t1
    | EBin (Ge, t1, t2) -> mk_bin t2 Le t1
    | EUn (Not, { texpr = EBin (Lt, t1, t2); _ }) -> mk_bin t2 Le t1
    | EUn (Not, { texpr = EBin (Le, t1, t2); _ }) -> mk_bin t2 Lt t1
    | EUn (Not, { texpr = EBin (Ge, t1, t2); _ }) -> mk_bin t1 Lt t2
    | EUn (Not, { texpr = EBin (Gt, t1, t2); _ }) -> mk_bin t1 Le t2
    | _ -> t
  in
  let rec apply_until_stable k t =
    let t' = Transform.apply_rule rule t in
    if ACES.equal t' t || k <= 0 then t' else apply_until_stable (k - 1) t'
  in
  apply_until_stable 0 t

let weaken ~(hyp : term list) (t : term) : term =
  let hyp = List.map ~f:norm_comparison hyp in
  let t = norm_comparison t in
  let subs =
    let f t = match t.texpr with EBin ((Lt | Le | Impl | Or), a, b) -> [ (a, b) ] | _ -> [] in
    List.concat (List.map ~f hyp)
  in
  apply_substs_ac subs t

let to_dnf t =
  let rule t0 =
    match t0.texpr with
    | EUn (Not, t1) -> (
        match t1.texpr with
        | EBin (And, t2, t3) -> mk_or (mk_not t2) (mk_not t3)
        | EBin (Lt, t2, t3) -> mk_bin t2 Ge t3
        | EBin (Le, t2, t3) -> mk_bin t2 Gt t3
        | EBin (Gt, t2, t3) -> mk_bin t2 Le t3
        | EBin (Ge, t2, t3) -> mk_bin t2 Lt t3
        | _ -> t0)
    | EBin (And, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EBin (Or, t3, t4), _ -> mk_or (mk_and t3 t2) (mk_and t4 t2)
        | _, EBin (Or, t3, t4) -> mk_or (mk_and t1 t3) (mk_and t1 t4)
        | _ -> t0)
    | _ -> t0
  in
  let rec apply_until_stable k t =
    let t' = Transform.apply_rule rule t in
    if ACES.equal t' t || k <= 0 then t' else apply_until_stable (k - 1) t'
  in
  let t1 = apply_until_stable 100 t in
  let brk_or t =
    let rd : term list Transform.recursor =
      {
        init = [];
        join = ( @ );
        case =
          (fun f t ->
            match t.texpr with EBin (Or, t1, t2) -> Some (f t1 @ f t2) | _ -> Some [ t ]);
      }
    in
    match Transform.recurse rd t with _ :: _ as t' -> t' | _ -> [ t ]
  in
  brk_or t1

let to_cnf tl =
  let if_rule t =
    match t.texpr with
    | EIte (c, tt, tf) -> mk_and (mk_or tt tf) (mk_and (mk_or (mk_not c) tt) (mk_or c tf))
    | _ -> t
  in
  let dist_and_or t =
    match t.texpr with
    | EBin (Or, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EBin (And, a, b), _ -> mk_bin (mk_bin a Or t2) And (mk_bin b Or t2)
        | _, EBin (Or, a, b) -> mk_bin (mk_bin t1 Or a) And (mk_bin t1 Or b)
        | _ -> t)
    | _ -> t
  in
  let brk_and t =
    let rd : term list Transform.recursor =
      {
        init = [];
        join = ( @ );
        case =
          (fun f t ->
            match t.texpr with EBin (And, t1, t2) -> Some (f t1 @ f t2) | _ -> Some [ t ]);
      }
    in
    match Transform.recurse rd t with _ :: _ as t' -> t' | _ -> [ t ]
  in
  Transform.(
    apply_rule if_rule --> apply_rule AcTerm.not_rule --> apply_rule dist_and_or
    --> eval_const_parts --> brk_and)
    tl

let to_mcnf (t : term) =
  let rec gather cnd_path e =
    match e.texpr with
    | EIte (c, e1, e2) -> gather (cnd_path @ to_cnf c) e1 @ gather (cnd_path @ to_cnf (mk_not c)) e2
    | _ -> [ (cnd_path, e) ]
  in
  gather [] (normalize t)

let normalize_branches_mcnf ?(costly = []) (emcnf : mcnf) =
  List.map ~f:(fun (cond, e') -> (cond, normalize ~costly e')) emcnf

let pp_mcnf (formt : Formatter.t) (mcnf : (term list * term) list) =
  List.iter
    ~f:(fun (cond, e) ->
      Fmt.(
        pf formt "@[<hov 2>‣ %a@;@[%a@]@;%a@]@." (box TermPp.pp_term) cond
          (styled (`Fg `Red) string)
          " ⟼ " (box TermPp.pp_term) e))
    (List.map ~f:(fun (el, e) -> (mk_term (ETuple el), e)) mcnf)

let pp_mcnf_ext (formt : Formatter.t) (mcnf : (term list * term * term Array.t) list) =
  Fmt.(
    list (fun formt (cond, e, e0) ->
        pf formt "@[<hov 2>‣ %a@;%a@;%a@;⟅%a⟆@]@."
          (box (list ~sep:TermPp.sep_and TermPp.pp_term))
          cond
          (styled (`Fg `Red) string)
          " ⟼ " (box TermPp.pp_term) e
          (box (array ~sep:vert TermPp.pp_term))
          e0))
    formt
    (List.map ~f:(fun (el, e, a) -> (el, e, a)) mcnf)

let mcnf_branch_type (e : mcnf) = match e with (_, eb) :: _ -> type_of eb | [] -> Ok TTop

let unique_conjuncts (e : mcnf) =
  let cfield uc c = List.mem uc c ~equal:(fun a b -> ACES.(a = b || t_not a = b || a = t_not b)) in
  let f uc (cl, _) =
    let f' uc c = if cfield uc c then uc else uc @ [ c ] in
    List.fold_left ~f:f' ~init:uc cl
  in
  List.fold_left ~f ~init:[] e

let blast_max : term -> term =
  let _mutate f t =
    match t.texpr with
    | EBin (Max, x, y) ->
        let x' = f x in
        let y' = f y in
        Some (mk_ite (mk_bin x' Ge y') x' y')
    | EBin (Min, x, y) ->
        let x' = f x in
        let y' = f y in
        Some (mk_ite (mk_bin x' Ge y') y' x')
    | _ -> None
  in
  Transform.transform _mutate

let rebuild_max : term -> term =
  let _mutate f t =
    match t.texpr with
    | EIte (c, a, b) -> (
        let c = f c in
        let a = f a in
        let b = f b in
        match c.texpr with
        | EBin (comp, a', b') when Binop.(comp = Ge || comp = Gt) ->
            if ACES.(a = a' && b = b') then Some (mk_max a b)
            else if ACES.(a = b' && b = a') then Some (mk_min a b)
            else Some (mk_ite c a b)
        | EBin (comp, a', b') when Binop.(comp = Le || comp = Lt) ->
            if ACES.(a = a' && b = b') then Some (mk_min a b)
            else if ACES.(a = b' && b = a') then Some (mk_max a b)
            else Some (mk_ite c a b)
        | _ -> Some (mk_ite c a b))
    | _ -> None
  in
  Transform.transform _mutate
