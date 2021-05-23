open Base
open Collect
open Lang.AcTerm
open Lang.Analyze
open Lang.Normalize
open Lang.ResourceModel
open Lang.SolutionDescriptors
open Lang.Term
open Lang.TermPp
open Lang.Typ
open Lang.Unfold
open Sexplib
open Solve.STerm
open Solve.SolverForms
open SymbExe
open SketchBuilders
open Utils
module Lt = ListTools
module Rd = RecursionDiscovery
module Smt = Solve.SmtLib
module TU = Lang.TermUtils

(* Result of discovery:
    - each element of the list corresponds to an element of the tuple-state.
    - each element is a result type, either the s-exp for the error or a list of auxilaries.
    - a this point an auxiliary is a variable and an expression defining the recursion.
*)
type lifting = { lifted_var : variable; liftings : (variable * term) list }

type discover_result = {
  auxiliaries : (local_context * lifting * term option) list IM.t;
  predicates : term list;
  errors : Sexp.t list;
}

(*======================================================================================== *)
(* ======================================== Pretty printing. ============================= *)
(*======================================================================================== *)

let pp_res_discover (format : Formatter.t) (r : discover_result) : unit =
  if not (Map.is_empty r.auxiliaries) then (
    Fmt.(pf format "Auxiliaries:@.");
    Map.iteri
      ~f:(fun ~key:i ~data:auxils ->
        Fmt.(
          pf format "--Var #%i:@.%a" i
            (list
               ~sep:(fun frmt () -> pf frmt "@.")
               (fun frmt (ctx, lifting_info, _) ->
                 pf frmt "--  Context %a:@.--  = %a@." pp_local_context ctx
                   (list (pair pp_variable (box pp_term)))
                   lifting_info.liftings)))
          auxils)
      r.auxiliaries );
  if not (List.is_empty r.predicates) then (
    Fmt.(pf format "Predicates:@.");
    List.iter ~f:(fun t -> Fmt.(pf format "--%a@." pp_term t)) r.predicates );
  if not (List.is_empty r.errors) then (
    Fmt.(pf format "Warnings:@.");
    List.iter ~f:(fun e -> Log.warning (printer_msg "%a" Sexp.pp_hum e)) r.errors )

(* ======================================================================================== *)
(* ========================= Auxiliary and predicate discovery ============================ *)
(* ======================================================================================== *)

let extract_u u si =
  let first_u = List.hd_exn u.eqns_unfoldings in
  let s =
    match si.sf_ret with
    | TStruct (s, _) -> s
    | _ -> failwith "Should be a struct after sfsp translation."
  in
  let ul =
    match reduce (mk_struct_mem ~s si.sf_li u.zero_unfolding.from_symb) with
    | Ok { texpr = EList [ x ]; _ } -> x
    | Ok e -> e
    | _ -> failwith "Malformed types?"
  in
  let xmap =
    match reduce (mk_struct_mem ~s si.sf_li first_u.from_init) with
    | Ok { texpr = EList [ elt ]; _ } when not (Terms.equal elt first_u.input) -> Some elt
    | Ok _ -> None
    | _ -> failwith "Malformed types?"
  in
  (u.resources, ul, first_u.input, first_u.from_symb, xmap)

let mxy_components resource cb (a0, fa1, a1) (_x, _y, _accum) components =
  let filt (c, r) =
    if is_normal_form cb resource a1 r then
      let e1 = mk_binop_of_list_or_fst And c in
      let e1' = Option.map ~f:(fun t -> lambdify _x a0 (lambdify _y fa1 t)) e1 in
      Option.map ~f:(fun t -> purify_pred (VarSet.of_list [ _accum; _x; _y ]) t) e1'
    else None
  in
  let pred_disj, comp_auxs =
    let f (comp, mcnf) =
      let lpred, lauxs = List.unzip (List.filter_map mcnf ~f:filt) in
      (lpred, (comp, Set.union_list (module Terms) lauxs))
    in
    let disj, caux = List.unzip (List.map ~f components) in
    ( mk_binop_of_list_or_fst Or (List.concat disj),
      List.filter_map caux ~f:(fun (c, s) ->
          Option.map ~f:(fun x -> (c, x)) (mk_binop_of_list_or_fst And (Set.elements s))) )
  in
  let pred_accum =
    Option.map pred_disj ~f:(fun t ->
        let t' = simp_pred (simplify_easy t) in
        mk_and (mk_vt _accum) t')
  in
  (pred_accum, comp_auxs, None)

let mz_components resource cb (u2 : sfsp_unfolding_result option) (a0, fa1, _) (_x, _y, _z, _accum)
    components =
  if cb.c = 3 then
    let u2 = match u2 with Some u -> u | _ -> failwith "budget.c > 2 requires more unfoldings." in
    let rec alt_lamb v1 v2 l =
      match l with hd :: tl -> lambdify v1 a0 (lambdify _z fa1 hd) :: alt_lamb v2 v1 tl | _ -> []
    in
    let filt_anti (c, r) =
      let f t = purify_pred (VarSet.of_list [ _accum; _x; _y; _z ]) t in
      let c' = List.concat_map ~f:(fun t -> to_dnf t) c in
      if input_free u2 resource r then List.map (alt_lamb _x _y c') ~f else []
    in
    let unwrap x = fst (List.unzip (List.concat (List.map (snd x) ~f:filt_anti))) in
    List.concat (List.map ~f:unwrap components)
  else []

let pred_from_unfoldings predicate_args (u, u2) cb si =
  (* Create all arguments of the predicate. *)
  let struct_name, li_elt_type =
    match si.sf_pre.s.vtype with
    | TStruct (s, mems) ->
        let liet =
          match List.Assoc.find_exn mems ~equal:String.equal si.sf_li with
          | TList t -> t
          | _ -> failwith "Unexpected: sf_li should always be of type list."
        in
        (s, liet)
    | _ -> failwith "Pre should have a struct argument."
  in
  let input_elt_type = match (fst si.sf_input).vtype with TList t -> t | _ -> TTop in
  (* At least two inputs *)
  let _x = mk_var ~name:"$x" li_elt_type in
  let _y = mk_var ~name:"$y" (if cb.k > 0 then input_elt_type else li_elt_type) in
  let _z = mk_var ~name:"$z" input_elt_type in
  let _accum = mk_var ~name:"p" TBool in
  let resource, al0, a1, e1, map_ini = extract_u u si in
  let fa_elt = Option.value map_ini ~default:a1 in
  let components =
    match e1.texpr with
    | EStruct el -> List.map ~f:(fun (comp, e) -> (comp, to_mcnf e)) el
    | _ -> []
  in
  let m1, aux_reqs, joing =
    mxy_components resource cb (al0, fa_elt, a1) (_x, _y, _accum) components
  in
  let m3 = mz_components resource cb u2 (al0, fa_elt, a1) (_x, _y, _z, _accum) components in
  (* Lift and create input lists of the predicate. *)
  let si = if cb.k > 0 || List.length aux_reqs > 0 then lift_comp aux_reqs si else si in
  let x_l =
    mk_struct_mem ~s:struct_name si.sf_li
      (mk_app (mk_vt si.sf_func) [ mk_vt (List.nth_exn predicate_args 0) ])
  in
  let y_l =
    if cb.k > 0 then mk_vt (List.nth_exn predicate_args 1)
    else
      mk_struct_mem ~s:struct_name si.sf_li
        (mk_app (mk_vt si.sf_func) [ mk_vt (List.nth_exn predicate_args 1) ])
  in
  let z_ls =
    if List.length predicate_args > 2 then [ mk_vt (List.nth_exn predicate_args 2) ] else []
  in
  let build_pred_e m1 =
    let pred_xy =
      mk_foldl ~init:mk_true x_l
        ~f:
          (mk_lambda [ _x; _accum ]
             (mk_foldl ~init:(mk_vt _accum) y_l ~f:(mk_lambda [ _y; _accum ] m1)))
    in
    match (m3, z_ls) with
    | _ :: _, [ z_l ] ->
        let pred_xz, pred_yz, pred_zxy =
          ( TU.mk_fold_xz ~neg:(cb.m >= cb.c) m1 m3 _accum (_x, x_l) (_z, z_l) (_y, y_l),
            TU.mk_fold_xz ~neg:(cb.m >= cb.c) m1 m3 _accum (_y, y_l) (_z, z_l) (_x, x_l),
            if cb.c > cb.m then TU.mk_fold_xyz ~not_z:true m3 _accum (_x, x_l) (_y, y_l) (_z, z_l)
            else mk_true )
        in
        mk_and pred_xy (mk_and pred_zxy (mk_and pred_xz pred_yz))
    | _ -> pred_xy
  in
  let predic = Option.map ~f:(fun x -> build_pred_e x) m1 in
  Log.debug Fmt.(printer_msg "@[Predicate : %a@]" (option (box pp_term)) predic);
  Option.map ~f:(fun x -> (x, si, aux_reqs, joing)) predic

(**
  Deduce the predicate for a given budget and output the predicate function,
  and a guess of a join sketch conditional on that predicate.
*)
let deduce_predicate (unfoldings : sfsp_unfolding_result)
    (unfoldings2 : sfsp_unfolding_result option) (budget : cbudget) (base : std_soln) :
    bool * (variable list * term) option * std_soln * (string * term) list * term option =
  let predicate_args =
    List.map ~f:(fun _ -> mk_var ~name:"l" (fst base.sf_input).vtype) (List.range 0 budget.c)
  in
  if budget.k = budget.n then (true, Some (predicate_args, mk_true), base, [], None)
  else
    match pred_from_unfoldings predicate_args (unfoldings, unfoldings2) budget base with
    | Some (predicate, lifted_base, aux_reqs, jg) ->
        (false, Some (predicate_args, predicate), lifted_base, aux_reqs, jg)
    | None -> (false, None, base, [], None)

let discover_predicate_and_sketches (budget : cbudget) (base : std_soln) :
    (pred_soln list * (variable list * term)) option =
  let tstart = Unix.gettimeofday () in
  let unfoldings = SymbExe.sfsp_unfoldings base in
  let unfoldings2 = if budget.c > 2 then Some (SymbExe.sfsp_unfoldings base) else None in
  (* let norm_unfl =
       normalize_soln_unfoldings ~solver:unfoldings.solver ~cinit:unfoldings.zero_unfolding
         ~costly:unfoldings.resources unfoldings.eqns_unfoldings
     in *)
  let is_ptrue, maybe_predicate, base, lifting_reqs, join_guess =
    deduce_predicate unfoldings unfoldings2 budget base
  in
  let join_sketch = build_join_sketch is_ptrue budget (join_guess, lifting_reqs) base in
  let sketched_div_soln = if is_ptrue then None else Some (build_partition_divide budget base) in
  let out_of_dsketch predicate sd =
    let div_sk, div_out =
      let bs = Fmt.str "_%i_%i_%i_" budget.k budget.m budget.c in
      ( Utils.Naming.tmp_file ("div_sketch" ^ bs) Naming.ext_racket,
        Caml.Filename.temp_file ("div_output" ^ bs) "" )
    in
    {
      synt_time = Unix.gettimeofday () -. tstart;
      tmp_file_sk = div_sk;
      tmp_file_out = div_out;
      base;
      predicate;
      budget;
      divide = sd;
    }
  in
  match maybe_predicate with
  | Some predicate ->
      let div_solns =
        match sketched_div_soln with
        | Some divs -> List.map ~f:(fun d -> out_of_dsketch predicate (Some d)) divs
        | None -> [ out_of_dsketch predicate None ]
      in
      Log.success
        Fmt.(fun f () -> pf f "Predicate found in %4.2f s." (Unix.gettimeofday () -. tstart));
      Some (div_solns, join_sketch)
  | None -> None

(* ======================================================================================== *)
(* ==============           Lifting for divide (weaken predicate)       =================== *)
(* ======================================================================================== *)
let pred_core (pred_body : term) =
  let rec aux t =
    match t.texpr with
    | EFoldL (f, init, _) | EFoldR (f, init, _) -> (
        match f.texpr with
        | ELambda ([ _; s0 ], lam_body) ->
            let body' = replace_expr ~old:(mk_vt s0) ~by:init lam_body in
            aux body'
        | _ -> aux f )
    | EBin (And, t1, t2) -> aux t1 @ aux t2
    | _ -> [ t ]
  in
  aux pred_body

let replace_core (pred_body : term) (core : term) =
  let rec aux t =
    match t.texpr with
    | EFoldL (f, init, el) -> mk_foldl ~f:(aux f) ~init el
    | EFoldR (f, init, el) -> mk_foldr ~f:(aux f) ~init el
    | ELambda ([ _x; _accum ], body) ->
        let body' =
          match body.texpr with
          | EBin (And, { texpr = EVar (Var v); _ }, _) | EBin (And, _, { texpr = EVar (Var v); _ })
            ->
              if Variable.(v = _accum) then mk_and (mk_vt v) core else aux body
          | EBin (Or, { texpr = EVar (Var v); _ }, _) | EBin (Or, _, { texpr = EVar (Var v); _ }) ->
              if Variable.(v = _accum) then mk_or (mk_vt v) core else aux body
          | _ -> aux body
        in
        mk_lambda [ _x; _accum ] body'
    | ELambda (args, body) -> mk_lambda args (aux body)
    | _ -> t
  in
  aux pred_body

let lift_of_wpred (si : std_soln) (wpred : term) : (variable * (term -> term -> term)) list =
  let auxiliary y maybe_comp typ =
    let v = mk_var ~name:"aux" typ in
    let f x accum =
      let xf = match maybe_comp with Some (s, comp, _) -> mk_struct_mem ~s comp x | None -> x in
      let cond =
        match maybe_comp with
        | Some (s, comp, off) ->
            let subsp1 = List.map off ~f:(fun comp' -> (mk_struct_mem ~s comp' (mk_vt y), accum)) in
            apply_substs_ac subsp1
              (replace_expr ~old:(mk_struct_mem ~s comp (mk_vt y)) ~by:xf wpred)
        | None -> replace_expr ~old:(mk_vt y) ~by:xf wpred
      in
      mk_ite cond xf accum
    in
    (v, f)
  in
  match Set.elements (free_variables wpred) with
  | [ y ] -> (
      match (fst si.sf_input).vtype with
      | TList TInt -> [ auxiliary y None TInt ]
      | TList (TStruct (inp_s, mems)) ->
          let f (m, t) =
            let off = ListTools.remove_elt ~equal:String.equal m (ListTools.lfst mems) in
            auxiliary y (Some (inp_s, m, off)) t
          in
          List.map ~f mems
      | _ -> [] )
  | _ -> []

let lift_by_weakening (orig : pred_soln) =
  if orig.budget.k = 0 then (
    (* Constant space allowed *)
    let pred_args, pred_expr = orig.predicate in
    let invar = Option.value (snd orig.base.sf_input) ~default:mk_false in
    let pcore =
      match pred_core pred_expr with
      | [] -> mk_false
      | _ :: _ as l -> (
          match mk_binop_of_list_or_fst And l with
          | Some t -> ( match to_dnf (simplify_easy t) with hd :: _ -> hd | _ -> mk_false )
          | None -> failwith "Unexpected, length l > 0." )
    in
    let inv_core =
      match pred_core invar with
      | [] -> mk_false
      | _ :: _ as l -> (
          match mk_binop_of_list_or_fst And l with
          | Some t -> simplify_easy t
          | None -> failwith "Unexpected, length l > 0." )
    in
    let pcore' =
      let fv_pcore = free_variables pcore in
      match Set.elements (free_variables inv_core) with
      | x :: _ ->
          let inv_versn =
            List.map (Set.elements fv_pcore) ~f:(fun v ->
                replace_expr ~old:(mk_vt x) ~by:(mk_vt v) inv_core)
          in
          weaken ~hyp:inv_versn pcore
      | [] -> pcore
    in
    let new_base = lift_std_soln (lift_of_wpred orig.base inv_core) orig.base in
    let new_pred_expr =
      replace_expr ~old:(mk_vt orig.base.sf_func) ~by:(mk_vt new_base.sf_func)
        (replace_core pred_expr pcore')
    in
    Log.debug (printer_msg "New base: %a@." pp_std_soln_func new_base);
    let join_inputs =
      List.map
        ~f:(fun i -> mk_var ~name:("s" ^ Int.to_string i) new_base.sf_ret)
        (List.range 0 orig.budget.m)
    in
    let new_join_sketch = join_body_of_fields orig.budget new_base join_inputs [] in
    Some
      ( { orig with predicate = (pred_args, new_pred_expr); base = new_base },
        (join_inputs, new_join_sketch) ) )
  else None

(* ======================================================================================== *)
(* ============== Auxiliary and predicate discovery (splitting divides) =================== *)
(* ======================================================================================== *)
let discover_predicate (func : l_eqns) (x : variable) (for_v : variable)
    (preds : (term * Rd.unfolding_info) list) =
  let constr_pred =
    match preds with
    | hd :: tl ->
        if List.for_all tl ~f:(fun (pred_t, _) -> ACES.(pred_t = fst hd)) then Some hd
        else
          let p =
            List.map ~f:(fun (e, u) -> replace_expr ~old:u.Rd.iinput ~by:(mk_vt func.x) e) preds
          in
          let pexpr = simplify_full (mk_conj p) in
          Some (pexpr, snd hd)
    | _ -> None
  in
  let make_head_aux =
    let aux = mk_var ~name:(for_v.vname ^ "_aux") x.vtype in
    (aux, mk_vt aux)
  in
  let constant_pred_case (cp, ui) =
    (* Does it require addditional auxs? *)
    let cr = collect cp in
    let cp' = replace_expr ~old:ui.Rd.iinput ~by:(mk_vt x) cp in
    match Map.to_alist cr.aux_exprs with
    | [] -> (Some cp', None)
    | [ (_, e) ] ->
        if Terms.(e = ui.iinput) then (Some cp', Some make_head_aux) else (Some cp', None)
    | _ -> (None, None)
  in
  match constr_pred with Some cp -> constant_pred_case cp | None -> (None, None)

let discover_cond_aux ~(solver : online_solver) (unfoldings : normalized_unfolding list)
    (func : l_eqns) (stv : VarSet.t) (for_v : variable) =
  let project l i = Map.find_exn l i in
  let input_i nu i = (Map.find_exn nu.u i).input in
  let normalized_and_collected =
    let per_unfolding nu =
      let aux_mcnfs = collect_mcnf ~solver (project nu.from_symb_mcnf for_v.vid) in
      ( List.map ~f:(fun (lc, sp, e_mcnf) -> (lc, (sp, (input_i nu for_v.vid, e_mcnf)))) aux_mcnfs,
        Map.map ~f:(fun x -> x.from_init) nu.u )
    in
    List.map ~f:per_unfolding unfoldings
  in
  (* Group by local context. *)
  let group_by_context aus : (local_context * (term * Rd.unfolding_info) list) list =
    (* Get all contexts *)
    let all_ctxs =
      let fo all_ctxs (ctx, _) =
        if List.mem ~equal:equal_local_contexts all_ctxs ctx then all_ctxs else ctx :: all_ctxs
      in
      List.fold_left ~f:(fun ctxs (l, _) -> List.fold_left ~f:fo ~init:ctxs l) ~init:[] aus
    in
    (* For each context, get the unfoldings of the corresp. aux. Put empty if no unfolding *)
    let f l ctx0 =
      let collect_ctx (ctx : local_context) =
        List.fold_left
          ~f:(fun uinfos (unf, iothers) ->
            match List.Assoc.find ~equal:equal_local_contexts unf ctx with
            | Some (pred, (iinput, imcnf)) -> uinfos @ [ (pred, Rd.{ iinput; imcnf; iothers }) ]
            | None ->
                uinfos
                @ [ (mk_false, Rd.{ iinput = mk_empty_list; imcnf = [ ([], mk_none) ]; iothers }) ])
          ~init:[]
      in
      (ctx0, collect_ctx ctx0 aus) :: l
    in
    List.fold_left all_ctxs ~init:[] ~f
  in
  (* Then find a conditional auxiliary (and predicate) for each context. *)
  let discover_for_each_ctx ctxs =
    try
      let f (ctx, unfolding_infos_with_pred) =
        Log.debug
          (Fmt.styled `Underline (fun fmt () ->
               Fmt.pf fmt "Lift variable %a (%a):" pp_variable for_v pp_local_context ctx));
        let x, accs =
          Rd.(
            _state := stv;
            discover_conditional_recursion for_v solver (ListTools.lsnd unfolding_infos_with_pred))
        in
        let p, aux_acc = discover_predicate func x for_v unfolding_infos_with_pred in
        (ctx, x, accs @ Option.to_list aux_acc, p)
      in
      List.map ~f ctxs
    with _ ->
      Log.warning_msg ~level:5 "Error while searching for lifting for contexts.";
      []
  in
  let filt_real_lifting = List.filter ~f:(fun (_, _, liftings, _) -> List.length liftings > 0) in
  match filt_real_lifting (discover_for_each_ctx (group_by_context normalized_and_collected)) with
  | [] -> (
      let allv = List.map ~f:mk_vt (Set.elements func.vars) in
      let allres = resources_of_terms allv in
      match Map.find func.eqns for_v.vid with
      | Some eqn_i ->
          let erhs = simplify_full (normalize ~costly:allres eqn_i.erhs) in
          Rd.conditional_accumulator for_v func.x (Set.remove func.vars for_v) erhs
      | None -> [] )
  | _ as l -> l

(* ======================================================================================== *)
(* ======================================================================================== *)

(**
   * discover : Discover auxiliaries (conditional or not) and parallelizing predicate.
   * lift : with optimizations for equation systems.
*)
let discover_from_eqns_unfoldings (u : eqns_unfolding_result) (nus : normalized_unfolding list)
    (_ : cbudget) (func : l_eqns) =
  (* STEP 0 : Normalize all the unfoldings. *)
  let solver = u.solver in
  let auxiliaries =
    Map.map
      (Map.of_alist_exn (module Int) (VarSet.bindings (maybe_to_lift func)))
      ~f:(fun v ->
        Collect._costly := u.resources;
        let c = discover_cond_aux ~solver nus func func.vars v in
        List.map
          ~f:(fun (ctxt, lifted_var, auxs, p) -> (ctxt, { lifted_var; liftings = auxs }, p))
          c)
  in
  let pos =
    let a = Set.max_elt_exn func.collection_inputs in
    let f i t =
      let t' =
        List.fold (Set.elements func.vars)
          ~f:(fun acc v ->
            match (get_rhs func v.vid, get_init func v.vid) with
            | Some rhs, Some init ->
                let rhs0 =
                  replace_expr ~old:(mk_vt v) ~by:init
                    (replace_expr ~old:(mk_vt func.x) ~by:(mk_mem (mk_vt a) (-i - 1)) rhs)
                in
                let rhs1 = if is_false init then mk_not rhs0 else rhs0 in
                replace_expr ~old:(mk_vt func.x)
                  ~by:(mk_mem (mk_vt a) (-i))
                  (replace_expr ~old:(mk_vt v) ~by:rhs1 acc)
            | _ -> acc)
          ~init:t
      in
      simplify_full t'
    in
    let rec until_nonvariant i t =
      let t' = f i t in
      if Terms.(t' = t) || i > 12 then t' else until_nonvariant (i + 1) t'
    in
    let u0 = mk_conj (collect_positive_conditionals func) in
    (until_nonvariant 0 --> simplify_full) u0
  in
  Some { auxiliaries; predicates = [ pos ]; errors = [] }

(* When a subset of the equations is finite-state *)

let fs_copies (fs : VarSet.t) =
  let f accum v =
    List.fold ~f:(fun accum l -> accum @ [ l @ [ (v, false) ]; l @ [ (v, true) ] ]) ~init:[] accum
  in
  List.fold ~f ~init:[ [] ] (Set.to_list fs)

let make_copy (l : l_eqns) (ns : (variable * bool) list) : l_eqns =
  let new_vars_subs =
    let f accum1 (v, b) =
      match (b, v) with
      | false, _ -> accum1
      | true, v ->
          let new_var = mk_var ~name:(v.vname ^ "_aux") v.vtype in
          accum1 @ [ (v, new_var) ]
    in
    List.fold ~f ~init:[] ns
  in
  let vs = VarSet.of_list (List.map ~f:fst new_vars_subs) in
  let dep_on_new =
    let _l =
      ListTools.lfst
        (Map.to_alist
           (Map.filteri
              ~f:(fun ~key ~data:eqn ->
                (not (VarSet.has_vid l.liftings key))
                && (not (VarSet.has_vid vs key))
                && not (Set.is_empty (Set.inter vs eqn.edeps)))
              l.eqns))
    in
    List.map _l ~f:(fun vid ->
        match VarSet.find_by_id l.vars vid with
        | Some v -> (v, mk_var ~name:(v.vname ^ "_aux") v.vtype)
        | None -> failwith "Unexpected")
  in
  let new_vars_subs = new_vars_subs @ dep_on_new in
  let new_varset = VarSet.of_list (List.map ~f:snd new_vars_subs) in
  let old_varset = VarSet.of_list (List.map ~f:fst new_vars_subs) in
  let l_varset = l.vars $|| new_varset in
  let _, _, lstate, rstate = _struct_creation_helper l_varset in
  let varsubst v =
    match List.Assoc.find new_vars_subs ~equal:Variable.equal v with Some v' -> v' | None -> v
  in
  let appsub eqn =
    let f t =
      Lang.TermUtils.apply_substs (List.map ~f:(fun (o, n) -> (mk_vt o, mk_vt n)) new_vars_subs) t
    in
    { eqn with erhs = f eqn.erhs; edeps = VarSet.map varsubst eqn.edeps }
  in
  let new_eqs =
    let f ~key ~data accum =
      match VarSet.find_by_id old_varset key with
      | Some oldv -> (
          match List.Assoc.find new_vars_subs ~equal:Variable.equal oldv with
          | Some newv ->
              let data' = appsub data in
              let lifts = Set.add data.elifts newv in
              let opposite =
                if ETypes.(newv.vtype = TBool) && Set.mem vs oldv then
                  Lang.AcTerm.simplify_easy (mk_not data'.einit)
                else data.einit
              in
              accum
              @ [ (key, { data with elifts = lifts }) ]
              @ [ (newv.vid, { data' with einit = opposite; elifts = lifts }) ]
          | None -> failwith "Unexpected" )
      | None -> accum @ [ (key, data) ]
    in
    Map.fold ~f ~init:[] l.eqns
  in
  {
    l with
    lstate;
    rstate;
    vars = l_varset;
    eqns = Map.of_alist_exn (module Int) new_eqs;
    liftings = l.liftings $|| new_varset;
  }

let sketch_fss_joins (l : l_eqns) : l_eqns =
  (* TODO make this better. *)
  let f (eqn : eqn_info) = { eqn with ejoin = Either.Second (mk_ite mk_true eqn.erhs eqn.erhs) } in
  { l with eqns = Map.map ~f l.eqns }

let lift_finite_state (l : l_eqns) : l_eqns option =
  let fss =
    let bool_vars_nonconstant = Set.filter ~f:(fun v -> is_bool (mk_vt v)) l.vars in
    let rec select_fs bv =
      let closed =
        let f ~key ~data = VarSet.has_vid bv key && Set.is_empty (Set.diff data.edeps bv) in
        VarSet.of_list
          (List.filter_map
             ~f:(fun (i, _) -> VarSet.find_by_id l.vars i)
             (Map.to_alist (Map.filteri ~f l.eqns)))
      in
      if Set.equal closed bv then bv else select_fs closed
    in
    select_fs bool_vars_nonconstant
  in
  let deps_on =
    VarSet.of_list
      (ListTools.lsnd
         (Map.to_alist
            (Map.filter_map
               ~f:(fun (v, s) -> if Set.is_empty s then Some v else None)
               (l_eqns_mapvar l l.eqns ~f:(fun v eqn -> (v, Set.diff eqn.edeps (Set.add fss v)))))))
  in
  let nl =
    if Set.is_empty fss || Set.is_empty (Set.inter (fss $|| deps_on) (unsolved l)) then (
      Log.debug (wrap " ❌ No finite state extensions.");
      None )
    else (
      Log.debug (printer_msg " ✔ Finite state extensions %a." VarSet.pp fss);
      match fs_copies fss with
      | [] -> None
      | hd :: tl -> Some (List.fold ~f:make_copy ~init:l (hd :: tl)) )
  in
  Option.map nl ~f:(fun nl ->
      let nl = clean_l_eqns nl in
      let nl = make_lifts_transitive nl in
      sketch_fss_joins nl)

(* ======================================================================================== *)
(* ================================== LIFTING EQN SYSTEM ================================== *)
(* ======================================================================================== *)

let add_dr (dr : discover_result) (l : l_eqns) =
  let preexisting_conds = collect_conditionals l in
  let old_vars = l.vars in
  let auxiliaries =
    let f ~key:i ~data:ctxts =
      match VarSet.find_by_id l.vars i with
      | Some orig_var ->
          ( orig_var,
            List.concat
              (List.map (* For each context. *)
                 ~f:(fun (_, lifting_info, _) ->
                   List.map (* For each new auxliary. *)
                     ~f:(fun (v, e) ->
                       (v, replace_expr ~old:(mk_vt lifting_info.lifted_var) ~by:(mk_vt l.x) e))
                     lifting_info.liftings)
                 ctxts) )
      | None -> failwith "Lifted from a non-existing variable?"
    in
    Map.mapi ~f dr.auxiliaries
  in
  let add_aux_for_v ~key:_ ~data:(origv, eqs) l =
    let f _l (v, e) =
      let new_eqn_info =
        {
          erhs = e;
          ejoin = Either.Second e;
          edeps = Set.diff (Lang.Analyze.free_variables e) (VarSet.singleton l.x);
          elifts = VarSet.empty;
          einit = Solve.Sketching.init_term preexisting_conds l.collection_inputs e;
        }
      in
      let eqns_mod =
        let _f ~key ~data =
          if key = origv.vid then { data with elifts = Set.add data.elifts v } else data
        in
        Map.mapi ~f:_f _l.eqns
      in
      {
        _l with
        vars = Set.add _l.vars v;
        eqns = Map.add_exn eqns_mod ~key:v.vid ~data:new_eqn_info;
      }
    in
    List.fold ~f ~init:l eqs
  in
  let predicate =
    match (dr.predicates, l.predicate.texpr) with
    | [], _ -> l.predicate
    | hd :: tl, EEmpty -> mk_conj (hd :: tl)
    | hd :: tl, _ -> mk_conj (l.predicate :: hd :: tl)
  in
  let l_lifted = Map.fold ~f:add_aux_for_v ~init:l auxiliaries in
  update_struct_vars l_lifted.vars { l_lifted with vars = old_vars; predicate }

let lift_conditional (func : l_eqns) : bool * l_eqns =
  if !Log.verb_debug > 3 then Log.debug (wrap "✓ Lift conditional.");
  let u = eqns_unfoldings func in
  let cinit =
    Array.of_list_map ~f:snd (Map.to_alist (Map.map ~f:(fun eqn -> eqn.einit) func.eqns))
  in
  let normalized_unfoldings =
    normalize_eqns_unfoldings ~solver:u.solver ~cinit ~costly:u.resources u.eqns_unfoldings
  in
  let init_budget = { n = 1; k = 0; c = 2; m = 2 } in
  match discover_from_eqns_unfoldings u normalized_unfoldings init_budget func with
  | Some dr ->
      let new_func = add_dr dr func in
      (false, new_func)
  | None -> (false, func)

let lift_noncond (func : l_eqns) : bool * l_eqns =
  if !Log.verb_debug > 4 then Log.debug (wrap " ⚠ Lift non conditional.");
  let _ = eqns_unfoldings func in
  (false, func)

let lift ?(level = 0) (func : l_eqns) : bool * l_eqns =
  let has_conds =
    Map.fold
      ~f:(fun ~key:_ ~data t -> t || not (Set.is_empty data))
      ~init:false
      (Map.map ~f:(fun eqn -> Lang.Analyze.get_conditions eqn.erhs) func.eqns)
  in
  Log.info (printer_msg "Input eqn system:@;@[%a@]" pp_l_eqns func);
  Log.info (wrap "Searching for liftings..");
  let b, func = if has_conds then lift_conditional func else lift_noncond func in
  let func = update_deps func in
  let new_func = match lift_finite_state func with Some func -> update_deps func | None -> func in
  Log.info (fun fmt () -> Fmt.pf fmt "New function(%i):@;@[%a@]" level pp_l_eqns new_func);
  (b, new_func)
