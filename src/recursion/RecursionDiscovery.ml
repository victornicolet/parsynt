open Base
open Lang.Analyze
open Lang.AcTerm
open Lang.Term
open Lang.TermPp
open Lang.TermUtils
open Lang.Typ
open Lang.Normalize
open Option.Let_syntax
open Solve.STerm
open Solve.SolverForms
open Utils
module AC = Lang.AcTerm

let _state = ref VarSet.empty

let exponents_limit = 6

type branch = term list * term
(** ========== Summary types for readability ==========*)

type recursion_scheme =
  | Rec of (variable * variable * term) list (* New simple recursive definition. *)
  | Existing of int

(* Previous value of state variable (int) at current unfolding. *)

type annot_branch = {
  abcond : term list;
  abexpr : term;
  abprev : term;
  abrecs : recursion_scheme list;
  abothers : term IM.t;
  abothers_prev : term IM.t;
}

type unfolding_info = {
  imcnf : mcnf;
  (* The mcnf of the current unfolding. *)
  iinput : term;
  (* The input term of the current unfolding. *)
  iothers : term IM.t; (* The expressions of the other variables. *)
}

(* Record information necessary to synthesize a recursive scheme. *)
type recursion_instance = {
  rprev : term;
  (* Previous expression of unfolding. *)
  rcur : term;
  (* Current expression of unfolding. *)
  rinput : term;
  (* Expression of input at current unfolding. *)
  rothers_prev : term IM.t; (* Expression of state at previous unfolding. *)
}

type uinfo_pred = {
  comp_id : int;
  is_norm : bool;
  norm_subset : int list;
  coupled_mcnf : mcnf_extended;
}

let pp_recursion_scheme (f : Formatter.t) (rscm : recursion_scheme) =
  match rscm with
  | Rec eqs ->
      Fmt.(
        pf f "⟪ %a ⟫"
          (list ~sep:semicolon (pair ~sep:(fun ft () -> pf ft " →@;") pp_variable pp_term))
          (List.map ~f:(fun (x, _, t) -> (x, t)) eqs))
  | Existing i -> Fmt.(pf f "f⦀%i⦀" i)

(* let pp_recursion_instance (f : Formatter.t) (ri : recursion_instance) =
   Fmt.(pf f "State:@[%a@]Term:@[%a->%a@]Others:@[%a@]"
         VarSet.pp ri.rstatevar rpp_term ri.rcur rpp_term ri.rprev
         (list ~sep:sp (braces (pair int ~sep:comma rpp_term))) (Map.to_alist ri.rothers_prev)) *)

let compare_recursion_schemes a b =
  match (a, b) with
  | Rec eqs, Rec eqs' ->
      let _cmp (v, _, t) (v', _, t') =
        if v.vid = v'.vid then AC.ACES.compare t t' else compare v.vid v'.vid
      in
      List.compare _cmp eqs eqs'
  | Existing i, Existing i' -> compare i i'
  | Rec _, _ -> 1
  | _, Rec _ -> -1

let equal_recursion_scheme a b = compare_recursion_schemes a b = 0

let pp_annot_branch (f : Formatter.t) (ab : annot_branch) =
  Fmt.(
    pf f "[%a : %a (%a)]" (list ~sep:sp pp_term) ab.abcond pp_term ab.abexpr
      (list ~sep:sp pp_recursion_scheme)
      ab.abrecs)

(* ============================================================================= *)
(* ============== General helpers : subexpressions, recursion schemes ========== *)
(* ============================================================================= *)

let find_subexpression_mappings ~(auxv : term) ~(sub : term) (t0 : term) =
  let rem_ac_duplicates =
    let compare (c, t) (c', t') = if c = c' then AC.ACES.compare t t' else compare c c' in
    List.dedup_and_sort ~compare
  in
  let rec subexpr_matches t =
    if AC.ACES.(t = sub) then [ (0, t); (1, auxv) ]
    else
      match t.texpr with
      | EBin (op, t1, t2) ->
          let t1_matches = subexpr_matches t1 in
          let t2_matches = subexpr_matches t2 in
          rem_ac_duplicates
            (List.map
               ~f:(fun ((ca, a), (cb, b)) -> (ca + cb, { t with texpr = EBin (op, a, b) }))
               (List.cartesian_product t1_matches t2_matches))
      | EUn (op, t1) ->
          List.map ~f:(fun (c, e) -> (c, { t with texpr = EUn (op, e) })) (subexpr_matches t1)
      | EIte (c, t1, t2) ->
          let t1_matches = subexpr_matches t1 in
          let t2_matches = subexpr_matches t2 in
          let c_matches = subexpr_matches c in
          rem_ac_duplicates
            (List.map
               ~f:(fun ((cc, c'), ((ct1, t1'), (ct2, t2'))) ->
                 (ct1 + ct2 + cc, { t with texpr = EIte (c', t1', t2') }))
               (List.cartesian_product c_matches (List.cartesian_product t1_matches t2_matches)))
      | _ -> [ (0, t) ]
  in
  (* Matches will always be sorted from most substitutions to least substitutions. *)
  match List.map ~f:(fun (_, t) -> (auxv, t)) (subexpr_matches t0) with _ :: tl -> tl | [] -> []

let mask_computed_subexpressions (m : term IM.t) (t0 : term) : term list =
  let substs =
    let state i =
      match VarSet.find_by_id !_state i with Some v -> mk_vt v | None -> failwith "Var not found."
    in
    List.map ~f:(fun (i, t) -> (t, state i)) (Map.to_alist m)
  in
  let f (t, st) = List.map ~f:snd (find_subexpression_mappings ~auxv:st ~sub:t t0) in
  t0 :: List.concat (List.map ~f substs)

let substitute_computed_expressions ~comp_prev t =
  match Lang.Unfold.reduce ~env:{ evars = !_state; evals = comp_prev } t with
  | Ok t -> t
  | Error s ->
      Log.error (printer_msg "While substituting, %a occurred." Sexp.pp_hum s);
      failwith "substitute_computed_expressions"

(**
   Find recursion scheme f such that cur_expr = f(prev_expr, computed, input_var)
   Remark that input_var can be a record.
*)
let find_recursion_schemes ~ivar ~rvar rec_instance : recursion_scheme list =
  let _find_cur m = Map.max_elt (Map.filter ~f:(fun _e -> Terms.equal _e rec_instance.rcur) m) in
  let use_stv _t = find_subexpression_mappings ~auxv:(mk_vt rvar) ~sub:rec_instance.rprev _t in
  let rec_schemes =
    let f (v, t) =
      Rec [ (var_of_exn v, ivar, replace_expr ~old:rec_instance.rinput ~by:(mk_vt ivar) t) ]
    in
    match _find_cur rec_instance.rothers_prev with
    | Some (i, _) -> [ Existing i ] (* Value in the state, in the previous unfolding. *)
    | None ->
        List.map ~f
          (List.concat
             (List.map ~f:use_stv
                (mask_computed_subexpressions rec_instance.rothers_prev rec_instance.rcur)))
  in
  let _filter_map rscm =
    match rscm with
    | Rec schemes -> (
        let _filter (rv, xi, rt) =
          Set.is_subset (vars_of rt) ~of_:(VarSet.of_list [ rv; xi ] $|| !_state)
        in
        match List.filter ~f:_filter schemes with [] -> None | l -> Some (Rec l))
    | _ -> Some rscm
  in
  List.filter_map ~f:_filter_map rec_schemes

(* Checks if cur = rscm(prev) *)
let recursion_scheme_explains ~(solver : online_solver) ~(ri : recursion_instance)
    (rscm : recursion_scheme) =
  let comp_prev = ri.rothers_prev in
  let solver_eq_check e =
    match check_simple ~solver:(Some solver) (mk_not (mk_bin e Eq ri.rcur)) with
    | Unsat -> true
    | _ -> false
  in
  let explains =
    match rscm with
    | Rec [ (v, x, t) ] ->
        let t' = substitute_computed_expressions ~comp_prev t in
        let t'' =
          replace_expr ~old:(mk_vt x) ~by:ri.rinput (replace_expr ~old:(mk_vt v) ~by:ri.rprev t')
        in
        solver_eq_check t''
    | Existing i -> ( match Map.find comp_prev i with Some x -> solver_eq_check x | None -> false)
    | _ -> failwith "TODO: Implement check for multiple accumulators."
  in
  (if !Log.verb_debug >= 4 then
   Fmt.(
     pf stdout "@[<v 2> %a %a -> %a ? %b@]@." (box pp_recursion_scheme) rscm (box pp_term) ri.rprev
       (box pp_term) ri.rcur explains));

  explains

(* ============================= Main entry points: discovering recursion ============================== *)
(* Discover simple recursion schemes, limited to scalars for now. *)
type discover_context = {
  ctx_input_variable : variable;
  ctx_unfoldings : (term * term * term IM.t) list;
}

let discover_conditional_accumulator_reduction ?(name_hint = "aux") (solver : online_solver)
    (ctx : discover_context) : recursion_scheme option =
  let cacc_unfoldings =
    let f (x, t, io) =
      let t' = Lang.Normalize.normalize ~costly:!Collect._costly t in
      let t' = Transform.apply_bottom_up_rule Lang.Normalize.factor_rule t' in
      let io = Map.map ~f:simplify_easy io in
      let t' = mask_computed_subexpressions io (simplify_easy t') in
      if List.length t' > exponents_limit then failwith "Discovered too many contexts."
      else
        let rcs = List.map ~f:Collect.collect t' in
        let rcs =
          List.map
            ~f:(fun rc -> { rc with aux_exprs = Map.map ~f:(minimize_cost []) rc.aux_exprs })
            rcs
        in
        Log.debug ~level:5
          (printer_msg "Collect on acc unf.@;%a@." Fmt.(list Collect.pp_collect_result) rcs);
        (x, t, io)
    in
    List.map ~f ctx.ctx_unfoldings
  in
  if !Log.verb_debug > 5 then (
    Fmt.(
      pf stdout "%a@;%a@."
        (styled `Underline string)
        "Condition unfoldings are:"
        (box ~indent:2 (list ~sep:sp (parens (pair ~sep:comma pp_term pp_term))))
        (List.map ~f:f2of3 cacc_unfoldings));
    Fmt.(
      pf stdout "%a@;%a@."
        (styled `Underline string)
        "Other expressions:"
        (box ~indent:2 (list ~sep:vert (pp_map pp_term)))
        (List.map ~f:third cacc_unfoldings)));
  let rinputvar = ctx.ctx_input_variable in
  let get_rec_schemes rrecvar u0 u1ul =
    let _f ((_, rprev, _), rec_scm) (rinput, rcur, rothers) =
      let _x =
        let unf_info = { rprev; rcur; rinput; rothers_prev = rothers } in
        (unf_info, find_recursion_schemes ~ivar:rinputvar ~rvar:rrecvar unf_info)
      in
      ((rinput, rcur, rothers), rec_scm @ [ _x ])
    in
    List.fold_left ~f:_f ~init:(u0, []) u1ul
  in
  let most_general_scheme ur_l : recursion_scheme option =
    let f (_, rcs) =
      let _f' rc (ri, _) = recursion_scheme_explains ~solver ~ri rc in
      List.find ~f:(fun rc -> List.for_all ~f:(_f' rc) ur_l) rcs
    in
    List.find_map ~f (List.rev ur_l)
  in
  let from_unfoldings u0 u1 ul : recursion_scheme option =
    let accum_with_type t =
      let aux_var = mk_var ~name:name_hint t in
      let _, rec_schemes = get_rec_schemes aux_var u0 (u1 :: ul) in
      most_general_scheme rec_schemes
    in
    match type_of (snd3 u0) with Ok t -> accum_with_type t | _ -> None
  in
  match ctx.ctx_unfoldings with
  | u0 :: u1 :: ul -> from_unfoldings u0 u1 ul
  | _ ->
      Log.warning (wrap "No unfoldings?@.");
      None

(* ========== Helpers for conditional recursion. ========== *)
let covers_all_recs (solver : online_solver) (rscms : recursion_scheme list)
    (annotated_unfoldings : (term * annot_branch list) list) =
  if !Log.verb_debug >= 4 then
    Log.debug (printer_msg "Checking %a" Fmt.(box (list ~sep:sp pp_recursion_scheme)) rscms);
  (*
  Return true if the annotated branch is covered by the recursion scheme.
  Return also the annotated branch, with the covering recursive scheme indicated.
   *)
  let pair_covers_branch icur (a_branch : annot_branch) =
    let f rscm =
      recursion_scheme_explains ~solver rscm
        ~ri:
          {
            rprev = a_branch.abprev;
            rinput = icur;
            rcur = a_branch.abexpr;
            rothers_prev = IM.empty (* Not needed here. *);
          }
    in
    let cov = List.find ~f rscms in
    match cov with
    | Some r -> (true, { a_branch with abrecs = a_branch.abrecs @ [ r ] })
    | _ -> (false, a_branch)
  in
  let pair_covers_unf icur (unf : annot_branch list) =
    let rec _f l (c, b) =
      match l with
      | [] -> (c, b)
      | ab :: tl ->
          let b', nb = pair_covers_branch icur ab in
          _f tl (c @ [ nb ], b && b')
    in
    _f unf ([], true)
  in
  let new_unfs =
    let rec _f l =
      match l with
      | [] -> []
      | (icur, unf) :: tl ->
          let new_unf, b = pair_covers_unf icur unf in
          if b then (icur, new_unf) :: _f tl else []
    in
    _f annotated_unfoldings
  in
  let check = List.length new_unfs = List.length annotated_unfoldings in
  if !Log.verb_debug >= 4 then
    Log.debug
      (printer_msg "%a covers all recursion terms!@."
         Fmt.(box (list ~sep:sp pp_recursion_scheme))
         rscms);
  (check, new_unfs)

let extract_rec_scheme_pair (solver : online_solver) (all_rec_schemes : recursion_scheme list)
    (annotated_unfoldings : (term * annot_branch list) list) :
    ((recursion_scheme * recursion_scheme) * (term * annot_branch list) list) option =
  let all_pairs = ListTools.all_pairs all_rec_schemes in
  let maybe_new_unfs_and_recs =
    let rec _f x =
      match x with
      | [] -> None
      | (x1, x2) :: tl ->
          let b, nf = covers_all_recs solver [ x1; x2 ] annotated_unfoldings in
          if b then Some ((x1, x2), nf) else _f tl
    in
    _f all_pairs
  in
  maybe_new_unfs_and_recs

exception Annotation_Failure

(** Annotate branches of mcnf with information : previous expression on branch, and tan recursive
    forms  that build the new expression as a function of the previous expression. *)
let annotate ?(solver = None) (cprev : mcnf) (c : mcnf) : annot_branch list =
  let annot (cnd, e0) =
    match
      List.find cprev (* Which previous branch is 'implied' by the current branch? *)
        ~f:(fun (cnd_prev, _) ->
          is_unsat (check_simple ~solver (mk_not (mk_impl (mk_conj cnd) (mk_conj cnd_prev)))))
    with
    | Some (_, e_prev) ->
        Ok
          {
            abcond = cnd;
            abexpr = e0;
            abprev = e_prev;
            abrecs = [];
            abothers = IM.empty;
            abothers_prev = IM.empty;
          }
    | None ->
        Log.warning (printer2_msg "<%a> -> %a" Fmt.(list ~sep:sp pp_term) cnd pp_term e0);
        Error (Sexp.Atom "Failed to annotate")
  in
  match Result.combine_errors (List.map ~f:annot c) with
  | Ok l -> l
  | Error _ -> raise Annotation_Failure

let build_conditional_accumulation ~(for_v : variable) (solver : online_solver)
    ((f1, f2) : recursion_scheme * recursion_scheme) ~(other_unfoldings : term IM.t list)
    ~(cr_unfoldings : (term * annot_branch list) list) : recursion_scheme option =
  let unfoldings =
    match List.zip cr_unfoldings (ListTools.remove_last other_unfoldings) with
    | Ok lp -> lp
    | Unequal_lengths ->
        Log.warning (wrap "Other unfoldings and cr_unfoldings of different lengths.");
        List.map ~f:(fun x -> (x, IM.empty)) cr_unfoldings
  in
  let split_cond_unfs =
    let _f ((inp, unf), otherf) =
      let _, neg_part =
        let _classify i ab =
          if List.mem ab.abrecs f1 ~equal:equal_recursion_scheme then Either.First i
          else Either.Second i
        in
        List.partition_map (List.mapi ~f:_classify unf) ~f:identity
      in
      let unf_term =
        splitting_condition ~solver (List.map ~f:(fun ab -> (ab.abcond, ab.abexpr)) unf) neg_part
      in
      (inp, unf_term, otherf)
    in
    List.map ~f:_f unfoldings
  in
  match (f1, f2) with
  | Rec [ (v1, x, t1) ], Rec [ (v2, x', t2) ] -> (
      match
        discover_conditional_accumulator_reduction ~name_hint:(for_v.vname ^ "_aux") solver
          { ctx_input_variable = x; ctx_unfoldings = split_cond_unfs }
      with
      | Some (Rec [ (cond_v, x, cond_term) ]) ->
          let v_accum, t_accum =
            let t2 = replace_expr ~old:(mk_vt x') ~by:(mk_vt x) t2 in
            if v1.vid = v2.vid then (v1, mk_ite (mk_vt cond_v) t2 t1)
            else
              let t2' = replace_expr ~old:(mk_vt v2) ~by:(mk_vt v1) t2 in
              (v1, mk_ite (mk_vt cond_v) t2' t1)
          in
          Some (Rec [ (cond_v, x, cond_term); (v_accum, x, t_accum) ])
      | _ ->
          Log.warning (wrap "Condition recurrence synthesis failed.");
          Log.warning
            (printer_msg "Condition unfoldings were: %a"
               Fmt.(box (list ~sep:sp (parens (pair ~sep:comma pp_term pp_term))))
               (List.map ~f:f2of3 split_cond_unfs));
          None)
  | _ -> None

let make_cond_acc (v1, x1, t1) (v2, x2, t2) =
  match (t1.texpr, t2.texpr) with
  | EVar (Var v), EIte ({ texpr = EVar (Var v'); _ }, _, _t2) when v.vid = v1.vid && v'.vid = v1.vid
    ->
      let t2' = replace_expr ~old:(mk_vt x2) ~by:(mk_vt x1) _t2 in
      (x1, [ (v2, t2') ])
  | _ ->
      let t2' = replace_expr ~old:(mk_vt x2) ~by:(mk_vt x1) t2 in
      (x1, [ (v1, t1); (v2, replace_expr ~old:(mk_vt v1) ~by:t1 t2') ])

let compute_branch_rec solver (rinputvar, rrecvar) (l, ui_prev) ui_cur =
  let recursiveforms =
    let annotate_branch (ab_norec : annot_branch) : annot_branch =
      let branch_vprev =
        let _sm =
          Map.map ~f:(fun _e ->
              let simpl_expr =
                simplify_mcnf ~solver:(Some solver) ~assume:ab_norec.abcond
                  ~mcnf:(compress_mcnf ~solver (to_mcnf (blast_max _e)))
              in
              simpl_expr)
        in
        _sm ui_prev.iothers
      in
      {
        ab_norec with
        abrecs =
          (let rprev = ab_norec.abprev in
           let rcur, rinput = (ab_norec.abexpr, ui_cur.iinput) in
           let rothers_prev = branch_vprev in
           find_recursion_schemes ~ivar:rinputvar ~rvar:rrecvar
             { rprev; rcur; rinput; rothers_prev });
      }
    in
    List.map ~f:annotate_branch (annotate ~solver:(Some solver) ui_prev.imcnf ui_cur.imcnf)
  in
  (l @ [ (ui_cur.iinput, recursiveforms) ], ui_cur)

(** Discover the conditional recursion that computes the given unfoldings.
   unfoldings is a list of pairs, each pair being the expression at the current unfolding plus
   all the expressions computed by the parent function at the current unfolding.
*)
let discover_conditional_recursion (for_v : variable) (solver : online_solver)
    (unfoldings : unfolding_info list) : variable * (variable * term) list =
  (* A solver with all the declarations should be provided. *)
  (* For each unfolding, replace pairs of (previous term, current term) by a subexpression
     mapping (expression with a special variable). *)
  let from_unfoldings ui0 ui1 uis =
    let branch_type =
      match mcnf_branch_type ui0.imcnf with
      | Ok t -> t
      | Error (s, t, e) ->
          Log.error (fun f () ->
              Fmt.(pf f "type error in discover, %s : %a is not %a." s pp_term (mk_term e) pp_typ t));
          failhere Caml.__FILE__ "discover_conditional_rec" "Type error."
    in
    (* Fold over the unfoldings, discover subtree isomorphisms from one unfolding to the next. *)
    let%bind annot_unfs, _ =
      try
        Some
          (let aux_var = mk_var ~name:(for_v.vname ^ "_aux") branch_type in
           let inp_var = mk_var ~name:"x" branch_type in
           List.fold_left (ui1 :: uis)
             ~f:(compute_branch_rec solver (inp_var, aux_var))
             ~init:([], ui0))
      with Annotation_Failure -> None
    in
    (* How many different recursive functions do we need? *)
    let%bind all_rec_fs =
      let jn rfs ab_branch = rfs @ ab_branch.abrecs in
      Some
        (List.dedup_and_sort ~compare:compare_recursion_schemes
           (List.fold_left ~init:[]
              ~f:(fun rfs (_, unf) -> List.fold_left unf ~init:rfs ~f:jn)
              annot_unfs))
    in
    if !Log.verb_debug >= 4 then (
      Log.info (wrap "Recursion schemes:");
      List.iter
        ~f:(fun rec_scm -> Fmt.(pf stdout "\t\t@[%a@]@." pp_recursion_scheme rec_scm))
        all_rec_fs);
    let%bind (f1, f2), annot_unfs = extract_rec_scheme_pair solver all_rec_fs annot_unfs in
    build_conditional_accumulation ~for_v solver (f1, f2)
      ~other_unfoldings:(List.map ~f:(fun r -> r.iothers) unfoldings)
      ~cr_unfoldings:annot_unfs
  in
  let placeholder = mk_var ~name:"_P?_" TTop in
  match unfoldings with
  (* At least two unfoldings *)
  | u0 :: u1 :: uns -> (
      match from_unfoldings u0 u1 uns with
      (* Simple accumulator. *)
      | Some (Rec [ (v, x, t) ]) -> (x, [ (v, t) ])
      (* Condition, Conditional Accumulator. *)
      | Some (Rec [ (v1, x1, t1); (v2, x2, t2) ]) -> make_cond_acc (v1, x1, t1) (v2, x2, t2)
      | Some x ->
          Log.warning (printer_msg "Unrecognized form %a@." Fmt.(box pp_recursion_scheme) x);
          (placeholder, [])
      | None -> (placeholder, []))
  | _ -> failhere Caml.__FILE__ "discover_conditional_rec" "Need more than 1 unfoldings."

let conditional_accumulator (v : variable) (x : variable) (_ : VarSet.t) (t : term) :
    (local_context * variable * (variable * term) list * term option) list =
  let cond_build op1 c tacc =
    let cond_v = mk_var ~name:(Fmt.str "%s_aux" v.vname) TBool in
    let accum_v = mk_var ~name:(Fmt.str "%s_aux" v.vname) v.vtype in
    match tacc.texpr with
    | EBin (op2, _, _) when distributes op2 op1 ->
        let condacc = type_term_exn (mk_and (mk_vt cond_v) c) in
        let accum =
          let free_vars = Set.remove (free_variables tacc) x in
          let subs = List.map ~f:(fun fv -> (mk_vt fv, mk_vt accum_v)) (Set.elements free_vars) in
          type_term_exn (mk_ite condacc (apply_substs_ac subs tacc) (mk_vt accum_v))
        in
        [ ((op2, mk_vt v), v, [ (cond_v, condacc); (accum_v, accum) ], Some (mk_not c)) ]
    | _ -> []
  in
  match t.texpr with
  | EBin (op1, t1, t2) -> (
      match (t1.texpr, t2.texpr) with
      | EIte (c, tt, tf), EVar (Var v') when Variable.(v = v') ->
          if is_constant tf then cond_build op1 c tt
          else if is_constant tt then cond_build op1 (mk_not c) tf
          else []
      | _ -> [])
  | _ -> []
