open Base
open Lang.Typ
open Lang.Term
open Lang.TermUtils
open Lang.AcTerm
open Lang.ResourceModel
open Lang.Normalize
open Lang.Unfold
open SolverForms
open Utils
module Smt = SmtLib

let simplify_conditionals (solver : online_solver) (ct : term) : term =
  spush solver;
  let t' =
    Transform.transform
      (fun f t ->
        match t.texpr with
        | EIte (c, tb, fb) -> (
            let c' = f c in
            match c'.texpr with
            | EConst (CBool true) -> Some (f tb)
            | EConst (CBool false) -> Some (f fb)
            | _ -> (
                match check_simple ~solver:(Some solver) (mk_not c) with
                | Unsat -> Some (f tb)
                | _ -> (
                    match check_simple ~solver:(Some solver) c with
                    | Unsat -> Some (f fb)
                    | _ ->
                        spush solver;
                        sassert solver c;
                        let tb' = f tb in
                        spop solver;
                        spush solver;
                        sassert solver (mk_not c);
                        let fb' = f fb in
                        spop solver;
                        Some (simplify_easy (mk_ite c tb' fb')) ) ) )
        | _ -> None)
      ct
  in
  spop solver;
  t'

(* ======================================== MCNF helpers ========================= *)

(**
   Rebuild an expression from a multi-way conditional normal form.
   Requires calls to solver to infer the conditions.
*)
let rev_conds (m : mcnf) : mcnf = List.map ~f:(fun (c, t) -> (List.rev c, t)) m

let simplify_branches_assuming ?(assume = mk_true) (s : online_solver) (vars : VarSet.t)
    (inp : mcnf) : mcnf =
  let maybe_assume_term, _, _ = build_smt_term assume in
  let f_branch hyp_term (ct, e) =
    let t_to_opt_expr ec =
      let ot, _, _ = build_smt_term ec in
      match ot with
      | Some t -> (
          let rc = exec_command s (Smt.mk_simplify (Smt.mk_and (Smt.mk_not hyp_term) t)) in
          match get_exprs_of_response vars rc with
          | Ok el -> (
              match el with
              | hd :: _ -> if Terms.(hd = mk_false) then None else Some ec
              | [] ->
                  Log.error (wrap "No expressions in response.");
                  None )
          | Error e ->
              Log.warning ~level:5
                (printer_msg "Error in response. Simplification failed: %a" Smt.pp_smtTerm
                   (Smt.mk_and (Smt.mk_not hyp_term) t));
              Log.warning ~level:5 (printer_msg " %a@." Fmt.(list ~sep:sp Sexp.pp) e);
              None )
      | None -> None
    in
    (List.filter_map ~f:t_to_opt_expr ct, e)
  in
  match maybe_assume_term with
  | Some hyp_term -> List.map ~f:(f_branch hyp_term) inp
  | None ->
      Log.error
        (printer_msg "This term cannot be translated to smt:@.---> %a.@."
           Fmt.(box Lang.TermPp.pp_term)
           assume);
      failhere Caml.__FILE__ "simplify_branches_assuming" "Failed to write assumption as SMT term."

let simplify_conjunction (solver : online_solver) (conj : term list) =
  let conj = List.map ~f:Lang.AcTerm.simplify_easy conj in
  if List.exists ~f:has_branching conj then (
    spush solver;
    List.iter ~f:(sassert solver) conj;
    let conj = List.map ~f:(simplify_conditionals solver) conj in
    spop solver;
    List.filter ~f:(fun t -> not (is_true t)) conj )
  else conj

(* Rebuild an expression tree from the mcnf. To do so, use a solver. *)
let expr_of_mcnf solver (t : mcnf) =
  let split_branches s splitc =
    List.partition_tf ~f:(fun (bc, _) ->
        let cnj = mk_conj (splitc :: bc) in
        is_unsat (check_simple ~solver:(Some s) (mk_not cnj)))
  in
  let _, req_decls, vars = decls_of t in
  let local_solver =
    match solver with
    | Some s -> s
    | None ->
        let z3 = make_z3_solver () in
        declare_all z3 req_decls;
        z3
  in
  let rec aux_f t =
    match t with
    | branch0 :: _ -> (
        match branch0 with
        | c0 :: _, _ -> (
            let bt, bf = split_branches local_solver c0 t in
            match (bt, bf) with
            | [], c ->
                (*             Log.info (printer_msg "+MCNF %a@." pp_mcnf c); *)
                aux_f (simplify_branches_assuming ~assume:c0 local_solver vars (rev_conds c))
            | _, [] -> failwith "Malformed MCNF."
            | _ :: _, _ :: _ ->
                let et = aux_f (simplify_branches_assuming ~assume:c0 local_solver vars bt) in
                let ef =
                  aux_f (simplify_branches_assuming ~assume:(mk_not c0) local_solver vars bf)
                in
                mk_ite c0 et ef )
        | [], e -> e )
    | [] -> failhere Caml.__FILE__ "expr_of_mcnf" "Unreachable case"
  in
  let e = match t with [] -> mk_empty_list | _ -> aux_f t in
  if is_none solver then close_solver local_solver;
  e

let rec simplify_term ?(solver = None) ?(assume = []) ?(strategy = "default") (t : term) : term =
  match strategy with
  | "default" ->
      if List.length assume > 0 then simplify_mcnf ~solver ~assume ~mcnf:(to_mcnf t) else t
  | "z3" -> ( match z3_simplify ~solver t with Some x -> x | None -> t )
  | "conds" -> simplify_cond ~solver ~assume t
  | "blast_max" -> rebuild_max (simplify_cond ~solver ~assume (blast_max t))
  | _ -> failhere Caml.__FILE__ "simplify_term" "Not a valid strategy."

and simplify_mcnf ?(solver = None) ~assume:(assumptions : term list) ~mcnf:(m : mcnf) : term =
  (* Remove unreachable branches *)
  let reachable_mcnf _e =
    let cnd_implied (cnd, _) =
      is_unsat (check_simple ~solver (mk_not (mk_and (mk_conj assumptions) (mk_conj cnd))))
    in
    List.filter ~f:cnd_implied _e
  in
  (* Simplify remaining branch conditions and branch expressions. *)
  let e_mcnf' _e =
    let simpl_branch_cond (cnd, __e) =
      let cnd' =
        List.filter
          ~f:(fun c ->
            not (is_unsat (check_simple ~solver (mk_and (mk_conj assumptions) (mk_not c)))))
          cnd
      in
      (cnd', simplify_term ~solver ~assume:cnd' __e)
    in
    if List.is_empty assumptions then _e else List.map ~f:simpl_branch_cond (reachable_mcnf _e)
  in
  match List.find m ~f:(fun (cnd, _) -> List.is_empty cnd) with
  | Some (_, x) -> x
  | _ -> expr_of_mcnf solver (e_mcnf' m)

and simplify_cond ?(solver = None) ~assume:(assumptions : term list) (t : term) : term =
  match assumptions with
  | [] -> t
  | _ ->
      let leftorright cond =
        let conj_assumptions = mk_conj assumptions in
        if check_implication ~solver conj_assumptions ~implies:cond then (true, false)
        else if check_implication ~solver conj_assumptions ~implies:(mk_not cond) then (false, true)
        else (false, false)
      in
      Transform.transform
        (fun f _t ->
          match _t.texpr with
          | EIte (c, t1, t2) -> (
              let c' = f c in
              match leftorright c' with
              | true, false -> Some (f t1)
              | false, true -> Some (f t2)
              | _ -> Some (mk_ite c' (f t1) (f t2)) )
          | _ -> None)
        t

(**
   Compress a multi-way conditional form. When using
    the syntactic rules to obtain the mcnf, we will end
    up with unreachable branches. In compress_mcnf, we use
    a backend solver to remove these branches.
*)
let compress_mcnf ~(solver : online_solver) (t : mcnf) : mcnf =
  let elim_if_unsat terms (condl, term) =
    match condl with
    | _ :: _ -> (
        let condl = simplify_conjunction solver condl in
        match check_simple ~solver:(Some solver) (mk_conj condl) with
        | Sat | Unknown | SExps _ ->
            let s_term =
              simplify_term ~solver:(Some solver) ~assume:condl ~strategy:"blast_max" term
            in
            terms @ [ (condl, s_term) ]
        | Error s -> failwith ("Solver error: " ^ s)
        | Unsat -> terms )
    | [] -> [ ([], term) ]
  in
  (* let elim_duplicates t_mcnf (condl, term) =
     let has_equiv (elt, _) =
      match
        check_simple ~solver:(Some solver) (mk_not (mk_bin (mk_conj elt) Eq (mk_conj condl)))
      with./te
      | Unsat -> true
      | _ -> false
     in if List.exists ~f:has_equiv t_mcnf then t_mcnf else t_mcnf @ [(condl, term)]
     in *)
  let no_unsat_branches = List.fold_left ~f:elim_if_unsat ~init:[] t in
  (* List.fold_left ~f:elim_duplicates ~init:[] no_unsat_branches *)
  no_unsat_branches

let normalize_unfoldings ~solver ~(costly : resource list) unfoldings : normalized_unfolding list =
  let f s_i = compress_mcnf ~solver (to_mcnf (normalize s_i)) in
  let couple_branches all_c_mcnfs e_mcnf =
    let f (c, e) =
      let conc_state =
        Map.map ~f:(fun cm -> simplify_mcnf ~solver:(Some solver) ~assume:c ~mcnf:cm) all_c_mcnfs
      in
      let computed = Array.of_list (List.map ~f:snd (Map.to_alist conc_state)) in
      let e' = add_computed_attributes e ~prev:None ~cur:computed in
      (c, e', computed)
    in
    List.map ~f e_mcnf
  in
  let per_unfolding u =
    let from_symb_mcnf, from_init_mcnf, u =
      let fi i =
        let s_i = if i > -1 then reduce_exn (mk_mem u.from_symb i) else u.from_symb in
        normalize_branches_mcnf ~costly (f s_i)
      in
      match (u.from_symb.texpr, u.from_init.texpr) with
      | ETuple els, ETuple elc ->
          if List.length els = List.length elc then
            ( Map.of_alist_exn (module Int) (List.mapi ~f:(fun i _ -> (i, fi i)) els),
              Map.of_alist_exn (module Int) (List.mapi ~f:(fun j e -> (j, f e)) elc),
              Map.of_alist_exn
                (module Int)
                (List.map2_exn
                   ~f:(fun (j, from_symb) (_, from_init) ->
                     (j, { input = u.input; from_init; from_symb }))
                   (List.mapi ~f:(fun j e -> (j, e)) els)
                   (List.mapi ~f:(fun j e -> (j, e)) elc)) )
          else
            failhere Caml.__FILE__ "normalize_unfoldings"
              "Type mismatch between concrete and symbolic."
      | _ ->
          ( Map.of_alist_exn (module Int) [ (0, fi (-1)) ],
            Map.of_alist_exn (module Int) [ (0, f u.from_init) ],
            Map.of_alist_exn (module Int) [ (0, u) ] )
    in
    let compress_components = Map.map ~f:(fun m -> compress_mcnf ~solver m) in
    let from_symb_mcnf = compress_components from_symb_mcnf in
    let from_init_mcnf = compress_components from_init_mcnf in
    let from_symb_mcnf = Map.map ~f:(couple_branches from_init_mcnf) from_symb_mcnf in
    { u; from_symb_mcnf; from_init_mcnf }
  in
  List.map ~f:per_unfolding unfoldings

let normalize_eqns_unfoldings ~solver ~cinit ~(costly : resource list)
    (eqns_unfoldings : unfolding IM.t list) : normalized_unfolding list =
  let term_to_mcnf x = compress_mcnf ~solver (to_mcnf (normalize x)) in
  let couple_branches all_c_mcnfs e_mcnf =
    let f (prev, l) (c, e) =
      let conc_state =
        Map.map ~f:(fun cm -> simplify_mcnf ~solver:(Some solver) ~assume:c ~mcnf:cm) all_c_mcnfs
      in
      let computed = Array.of_list (List.map ~f:snd (Map.to_alist conc_state)) in
      let e' = add_computed_attributes e ~prev:(Some prev) ~cur:computed in

      (computed, l @ [ (c, e', prev) ])
    in
    List.fold ~init:(cinit, []) ~f e_mcnf
  in
  let per_eqns_unfolding eqnu =
    let per_unfolding sel ~key:_ ~data:u =
      let mcnf = normalize_branches_mcnf ~costly (term_to_mcnf (sel u)) in
      let mcnf = compress_mcnf ~solver mcnf in
      mcnf
    in
    let from_symbs = Map.mapi ~f:(per_unfolding (fun u -> u.from_symb)) eqnu in
    let from_init_mcnf = Map.mapi ~f:(per_unfolding (fun u -> u.from_init)) eqnu in
    let from_symb_mcnf = Map.map ~f:(couple_branches from_init_mcnf --> snd) from_symbs in
    { u = eqnu; from_symb_mcnf; from_init_mcnf }
  in
  List.map ~f:per_eqns_unfolding eqns_unfoldings

let normalize_soln_unfoldings ~solver ~cinit:_ ~(costly : resource list)
    (_unfoldings : unfolding list) =
  let term_to_mcnf x =
    let n_x, elapsed = timed normalize x in
    Log.debug ~level:3 (printer_msg "Normalize in %a s." Fmt.float elapsed);
    let m_x, elapsed = timed to_mcnf n_x in
    Log.debug ~level:3 (printer_msg "To mcnf in %a s." Fmt.float elapsed);
    let m_f, elapsed = timed (compress_mcnf ~solver) m_x in
    Log.debug ~level:3 (printer_msg "Compress in %a s." Fmt.float elapsed);
    m_f
  in
  let to_mcnf t =
    let m0 = term_to_mcnf t in
    normalize_branches_mcnf ~costly (compress_mcnf ~solver m0)
  in
  let per_unfolding unf =
    let this_unfolding sel =
      match (sel unf).texpr with
      | EStruct fields ->
          Map.of_alist_exn (module String) (List.map ~f:(fun (a, b) -> (a, to_mcnf b)) fields)
      | _ -> Map.empty (module String)
    in
    let from_symbs = this_unfolding (fun u -> u.from_symb) in
    let from_init = this_unfolding (fun u -> u.from_init) in
    Map.iter
      ~f:(fun mcnf ->
        Log.debug ~level:3 (printer_msg "@[Mcnf of unfolding:@;@[%a@]@]" pp_mcnf mcnf))
      from_symbs;
    (from_init, from_symbs)
  in
  List.map ~f:per_unfolding _unfoldings

let norm_cond_unfoldings (t : term) =
  Log.debug ~level:3 (wrap "Apply norm cond@.");
  let t = simplify_easy (Transform.apply_top_down_rule not_rule t) in
  rebuild_tree_AC ACES.compare (to_ac t)

(** Find a condition such that forall cond in cpos, cond => c.
    If possible, this condition should be minimal.
*)
let splitting_condition ~(solver : online_solver) (e : mcnf) (sube : int list) : term =
  let epos = List.(filteri ~f:(fun i _ -> mem sube i ~equal:( = ))) e in
  let eneg = List.(filteri ~f:(fun i _ -> not (mem sube i ~equal:( = )))) e in
  let check_valid_split s =
    List.for_all epos ~f:(fun (cnd, _) ->
        is_unsat (check_simple ~solver:(Some solver) (mk_and (mk_not s) (mk_conj cnd))))
    && List.for_all eneg ~f:(fun (cnd, _) ->
           is_unsat (check_simple ~solver:(Some solver) (mk_and s (mk_conj cnd))))
  in
  let conjs = unique_conjuncts e in
  let num_conjs = List.length conjs in
  let split_level i =
    let allk = List.(concat (map ~f:cond_possibilities (ListTools.k_combinations i conjs))) in
    let allsplits = List.(map ~f:mk_conj allk @ map ~f:mk_disj allk) in
    List.find ~f:check_valid_split allsplits
  in
  let rec find_split k =
    if k > num_conjs then mk_false
    else match split_level k with Some split -> split | None -> find_split (k + 1)
  in
  find_split 1
