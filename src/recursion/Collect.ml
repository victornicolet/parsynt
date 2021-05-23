open Base
open Lang.AcTerm
open Lang.Analyze
open Lang.Normalize
open Lang.ResourceModel
open Lang.Term
open Lang.Typ
open Lang.TermPp
open Solve.STerm
open Solve.SolverForms
open Utils
module Smt = Solve.SmtLib

let pp_collect_result (formt : Formatter.t) (cr : collect_result) : unit =
  Fmt.(
    pf formt "@[<v 2>【%a】@;<%a>@]" pp_term cr.context_tree
      (list ~sep:cut (parens (pair ~sep:arrow string pp_term)))
      (Map.to_alist cr.aux_exprs))

let pp_local_context (format : Formatter.t) ((bop, e) : local_context) : unit =
  Fmt.(pf format "ℭ ⦰ %a %a" pp_binop bop pp_term e)

let _costly : resource list ref = ref []

(** ======================================================================================== *)

(** ======================================================================================== *)

let get_local_context cr aux : local_context option =
  let is_t_aux v_t = match v_t.texpr with EVar (Var v) -> String.equal aux v.vname | _ -> false in
  let mjoin = Option.merge ~f:(fun a _ -> a) in
  Transform.recurse
    {
      init = None;
      join = mjoin;
      case =
        (fun _ t ->
          match t.texpr with
          | EBin (op, v2, e) when is_t_aux v2 -> Some (Some (op, e))
          | EBin (op, e, v2) when is_t_aux v2 -> Some (Some (op, e))
          (* TODO conditional cases *)
          | EIte (_, _, v2) when is_t_aux v2 -> Some None
          | EIte (_, v2, _) when is_t_aux v2 -> Some None
          | EIte (v2, _, _) when is_t_aux v2 -> Some None
          | _ -> None);
    }
    cr.context_tree

let compare_local_contexts (op1, e1) (op2, e2) =
  if Binop.equal op1 op2 then Terms.compare e1 e2 else Binop.compare op1 op2

let equal_local_contexts c1 c2 = compare_local_contexts c1 c2 = 0

(** Returns the list of local contexts of the auxiliaries that need to be
    collected given a collection result.
    Returns a list with triples (variable name, expression to be collected,
    local context).
*)
let cr_as_local_contexts cr : (string * term * local_context) list =
  Map.fold cr.aux_exprs ~init:[] ~f:(fun ~key:k ~data:e l ->
      let key_ctx = get_local_context cr k in
      match key_ctx with Some ctx -> (k, e, ctx) :: l | None -> l)

(** Returns an identity element corresponding to a local context, if possible. *)
let loc_ctx_identity_elt (op, _) = Option.(Lang.AcTerm.ident_elt op >>| mk_term)

let uses_resources (resources : resource list) (t : term) =
  let f res = match res with RScalar s -> ACES.(s = t) | RList lt -> all_subterms_in t ~mem:lt in
  List.exists ~f resources

(* ======================================== COLLECT ============================== *)
(* Entry point for collecting auxiliaries for a single expression (not a mcnf). *)
let collect ?(mask : term list = []) (tin : term) : collect_result =
  let is_costly e = uses_resources !_costly e in
  let new_context_var t = mk_var ~name:"ctx" t in
  let empty_esmap = Map.empty (module String) in
  let single_esmap = Map.singleton (module String) in
  let not_in_mask t = not (List.mem ~equal:ACES.equal mask t) in
  let key_pick_left ~key:_ v =
    match v with `Both (v1, _) -> Some v1 | `Left v1 -> Some v1 | `Right v2 -> Some v2
  in
  let join_esmap a b = Map.merge ~f:key_pick_left a b in
  (*
    Gather expressions that sit next to a costly expression, unless they are in the mask.
    Input expressions should be in fully reduced form.
  *)
  let gather_aux e =
    let recr =
      Transform.
        {
          init = empty_esmap;
          join = join_esmap;
          case =
            (fun f e ->
              let not_c eo =
                let e', m = f eo in
                (* Empty map means no auxilary under this case. *)
                if Map.is_empty m then (
                  match type_of eo with
                  | Ok teo ->
                      let x = new_context_var teo in
                      (mk_vt x, single_esmap x.vname eo)
                  | Error _ ->
                      ( if !Log.verb_debug = 3 then
                        Fmt.(pf stdout "[collect] Type error in %a.@." pp_term eo) );
                      (eo, m) )
                else (e', m)
              in
              match e.texpr with
              | EBin (op, e1, e2) -> (
                  match (is_costly e1, is_costly e2) with
                  | true, true -> Some (mk_bin e1 op e2, empty_esmap)
                  | true, false when not_in_mask e2 ->
                      let e', m = not_c e2 in
                      Some (mk_bin e1 op e', m)
                  | false, true when not_in_mask e1 ->
                      let e', m = not_c e1 in
                      Some (mk_bin e' op e2, m)
                  (* Should not happen, since (case e) is true. *)
                  | _ -> None )
              | EIte (c, e1, e2) -> (
                  if is_costly c then
                    match (is_costly e1, is_costly e2) with
                    | true, true -> Some (mk_ite c e1 e2, empty_esmap)
                    | true, false when not_in_mask e2 ->
                        let e', m = not_c e2 in
                        Some (mk_ite c e1 e', m)
                    | false, true when not_in_mask e1 ->
                        let e', m = not_c e1 in
                        Some (mk_ite c e' e2, m)
                    | _ -> None
                  else
                    let c', ac = f c in
                    match (is_costly e1, is_costly e2) with
                    | true, true -> Some (mk_ite c' e1 e2, ac)
                    | true, false when not_in_mask e2 ->
                        let e', m = not_c e2 in
                        Some (mk_ite c' e1 e', join_esmap ac m)
                    | false, true when not_in_mask e1 ->
                        let e', m = not_c e1 in
                        Some (mk_ite c' e' e2, join_esmap ac m)
                    (* Should not happen, since (case e) is true. *)
                    | _, _ ->
                        let (e1', a1), (e2', a2) = (f e1, f e2) in
                        Some (mk_ite c e1' e2', join_esmap ac (join_esmap a1 a2)) )
              | _ -> None);
        }
    in
    let ctx_ast, smap = Transform.transform_and_recurse recr e in
    { context_tree = ctx_ast; aux_exprs = smap }
  in
  let collect_res = gather_aux tin in
  { collect_res with aux_exprs = Map.map ~f:simplify_easy collect_res.aux_exprs }

(** Collect auxiliaries in mcnf.
    @param costly an optional argument indicating which terms are considered costly in the
      cost-directed normalization heuristic.
    @param t  an extended mcnf, with noremalized branches.
    @returns a list of potential auxiliaries, one for each local context.
*)
let collect_mcnf ~(solver : online_solver) (t0 : mcnf_extended) : (local_context * term * mcnf) list
    =
  ( if !Log.verb_debug > 5 then
    Fmt.(
      pf stdout "%a@.@[%a@]@." (styled `Underline string) "Collect for input mcnf:" pp_mcnf_ext t0)
  );
  let collected_results () =
    List.map t0 ~f:(fun (cond, e, computed) ->
        let x = collect ~mask:(Array.to_list computed) e in
        (cond, cr_as_local_contexts x))
  in
  let aux_with_contexts () =
    let merge_branches assoc (i, (bc, loc_ctx_li)) =
      let merge_loc_ctx (i : int) (cond : cond) assoc (aux_name, aux_t, loc_ctx) =
        match List.Assoc.find assoc loc_ctx ~equal:equal_local_contexts with
        | Some (aux_name0, cond_el) ->
            (* Add new branch and new alias *)
            let updated = (aux_name0, cond_el @ [ (i, (cond, aux_t)) ]) in
            (* WARNING: Documentation on Assoc.add doesn't specify if add removes prev binding. *)
            List.Assoc.add assoc ~equal:equal_local_contexts loc_ctx updated
        | None ->
            (* New branch and new ctx, add other branches if identity for ctx *)
            let extra_branches =
              match (List.hd assoc, loc_ctx_identity_elt loc_ctx) with
              | Some (_, (_, mcnf_aux)), Some elt0 ->
                  List.map ~f:(fun (j, (c, _)) -> (j, (c, elt0))) mcnf_aux
              | _, _ -> []
            in
            (loc_ctx, (aux_name, extra_branches @ [ (i, (cond, aux_t)) ])) :: assoc
      in
      List.fold_left ~f:(merge_loc_ctx i bc) ~init:assoc loc_ctx_li
    in
    List.fold_left ~f:merge_branches ~init:[] (ListTools.index (collected_results ()))
  in
  let sub_mcnf_per_ctx =
    if List.length t0 < 9 then
      List.map
        ~f:(fun (ctx, (_, mcnf)) ->
          let indexs = ListTools.lfst mcnf in
          let split_pred =
            splitting_condition ~solver (List.map ~f:(fun (x, y, _) -> (x, y)) t0) indexs
          in
          (ctx, split_pred, ListTools.deindex mcnf))
        (aux_with_contexts ())
    else []
  in
  if !Log.verb_debug > 5 then
    List.iter sub_mcnf_per_ctx ~f:(fun (c, p, m) ->
        Fmt.(
          pf stdout "---- For context %a, mcnf:@;%a@.    Splitting predicate: %a@." pp_local_context
            c pp_mcnf m pp_term p));
  sub_mcnf_per_ctx

let rec is_normal_form (b : cbudget) (res : resource list) (a0 : term) (t0 : term) =
  match t0.texpr with
  | EList [ t1 ] -> uses_resources res t1 && b.k > 0
  | EList [ t1; t2 ] ->
      uses_resources res t1 && (b.k > 0 || Set.equal (free_variables t2) (free_variables a0))
  | EBin ((Plus | Minus | Times), t1, t2) ->
      if uses_resources res t1 then Set.equal (free_variables t2) (free_variables a0) || b.k > 0
      else if uses_resources res t2 then
        Set.equal (free_variables t1) (free_variables a0) || b.k > 0
      else false
  | EBin (Concat, t1, t2) ->
      if uses_resources res t1 then
        match t2.texpr with
        | EList [ x ] -> ACES.equal x a0
        | _ -> Set.equal (free_variables t2) (free_variables a0) || b.k > 0
      else false
  | EUn (_, t) -> is_normal_form b res a0 t
  | EVar (Var v) -> (
      match v.vtype with TBool -> uses_resources res t0 (* ~ t0 \or v *) | _ -> false )
  | _ -> false

let input_free _ (res : resource list) (t0 : term) =
  match t0.texpr with
  | EList [ t1 ] -> uses_resources res t1
  | EList [ t1; t2 ] -> uses_resources res t1 && uses_resources res t2
  | EBin (Concat, t1, t2) -> uses_resources res t1 && uses_resources res t2
  | EConst _ -> true
  | _ -> false
