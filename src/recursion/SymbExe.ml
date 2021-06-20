open Base
open Fmt
open Lang.AcTerm
open Lang.SolutionDescriptors
open Lang.ResourceModel
open Lang.Term
open Lang.TermPp
open Lang.Typ
open Lang.Unfold
open Solve.SolverForms
open Utils

let allow_nonlinear = ref false

type unfoldings_result = {
  state_record_var : VarSet.t;
  (* Variable used as record in the unfoldings.  *)
  init_as_resource : resource list;
  (* Symbolic vars used as starting state of unfoldings. *)
  unfoldings : unfoldings;
  (* The unfoldings ( a list of unfolding)  *)
  solver : online_solver;
  (* A solver initialized with all symbols. *)
  ret_type : typ list; (* Return type of the function, used for projection. *)
}

let symbexe_verbose = ref 0

let use_solver_eval = ref true

let solver_of_unfoldings (unfoldings : unfoldings) : online_solver option =
  let symbs = List.map ~f:(fun x -> x.from_symb) in
  let _, decls1, _ = build_terms (symbs unfoldings) in
  let z3 = make_z3_solver () in
  declare_all z3 decls1;
  Some z3

let branching_eval (solver : online_solver) (env : env) (t : term) =
  let rec eval_var env v = find_binding v env
  and branch env c0 f1 f2 =
    let c = simplify_easy (eval_term env c0) in
    if is_true c then f1 ()
    else if is_false c then f2 ()
    else
      match check_simple ~solver:(Some solver) (mk_not c) with
      | Unsat ->
          spush solver;
          let e1' = f1 () in
          spop solver;
          e1'
      | _ -> (
          match check_simple ~solver:(Some solver) c with
          | Unsat ->
              spush solver;
              let e2' = f2 () in
              spop solver;
              e2'
          | _ ->
              spush solver;
              sassert solver c;
              let e1' = f1 () in
              spop solver;
              spush solver;
              sassert solver (mk_not c);
              let e2' = f2 () in
              spop solver;
              mk_ite c e1' e2')
  and eval_mem env tuple index =
    match (eval_term env tuple).texpr with
    | ETuple tl -> (
        match List.nth tl index with
        | Some t -> eval_term env t
        | None -> failhere Caml.__FILE__ "eval_mem" "Out of bounds.")
    | EIte (c, t1, t2) ->
        branch env c
          (fun () -> eval_term env (mk_mem t1 index))
          (fun () -> eval_term env (mk_mem t2 index))
    | tuple' -> mk_mem (mk_term tuple') index
  and eval_struct_field env struc sn mn =
    match (eval_term env struc).texpr with
    | EStruct mems -> (
        match List.Assoc.find mems ~equal:String.equal mn with
        | Some t -> eval_term env t
        | None -> failhere Caml.__FILE__ "eval_struct_mem" "Invalid member.")
    | EIte (c, t1, t2) ->
        branch env c
          (fun () -> eval_term env (eval_struct_field env t1 sn mn))
          (fun () -> eval_term env (eval_struct_field env t2 sn mn))
    | struc' -> mk_struct_mem ~s:sn mn (mk_term struc')
  and eval_term env t =
    match t.texpr with
    | ELet (Var v, e1, e2) ->
        let e1' = eval_term env e1 in
        eval_term (add_binding v e1' env) e2
    | EPLet (bindings, e2) ->
        let bindings' = List.map ~f:(fun (v, e) -> (v, eval_term env e)) bindings in
        eval_term (add_bindings bindings' env) e2
    | EVar (Var v) -> ( match eval_var env v with Some t -> t | None -> mk_vt v)
    | EEmpty | EHole _ -> t
    | EMem (tuple, index) -> eval_mem env tuple index
    | EMemStruct (sn, mn, struc) -> eval_struct_field env struc sn mn
    | EConst _ -> t
    | EBin (b, e1, e2) -> (
        match b with
        | Concat -> mk_concat (eval_term env e1) (eval_term env e2)
        | Cons -> mk_cons (eval_term env e1) (eval_term env e2)
        | _ -> mk_bin (eval_term env e1) b (eval_term env e2))
    | EUn (u, e1) -> mk_un u (eval_term env e1)
    | ETuple el -> mk_tuple (List.map ~f:(eval_term env) el)
    | EList el -> mk_list (List.map ~f:(eval_term env) el)
    | EChoice el -> (
        match mk_choice (List.map ~f:(eval_term env) el) with
        | Ok t -> t
        | Error te ->
            typecheck_err te;
            failwith "Symbexe type error.")
    | EStruct fields ->
        let f (s, t) = (s, eval_term env t) in
        mk_struct (List.map ~f fields)
    | EIte (c0, e1, e2) -> branch env c0 (fun () -> eval_term env e1) (fun () -> eval_term env e2)
    | ELambda _ -> t
    | EApp (f, args) -> eval_app env f args
    | EFoldL (f, ei, le) -> eval_fold env f ei le
    | EWith _ | ESetL _ -> failwith "TODO : symbexe with with and set"
    | ELetValues _ | EFoldR _ -> failwith "Unsupported"
  and eval_app env fterm args =
    match (eval_term env fterm).texpr with
    | ELambda (argsv, lbody) -> (
        match List.map2 ~f:(fun v e -> (v.vid, eval_term env e)) argsv args with
        | List.Or_unequal_lengths.Ok l -> (
            match Map.of_alist (module Int) l with
            | `Duplicate_key _ ->
                raise (SymbExeError ("lambda refers to same variable twice", fterm))
            | `Ok vals ->
                eval_term (env_extend env { evars = VarSet.of_list argsv; evals = vals }) lbody)
        | List.Or_unequal_lengths.Unequal_lengths ->
            raise
              (SymbExeError ("lambda application has wrong number of args, cannot branch", fterm)))
    | e ->
        Fmt.(Log.error (fun f () -> pf f "Cannot apply: %a." pp_term (mk_term e)));
        Fmt.(Log.error (fun f () -> pf f "Env was: %a." pp_env env));
        failwith "TODO"
  and eval_fold env fterm init0 tlist =
    let init = eval_term env init0 in
    let fterm = eval_term env fterm in
    let f acc inpt = eval_app env fterm [ inpt; acc ] in
    match (eval_term env tlist).texpr with
    | EConst CEmpty -> eval_term env init
    | EList lt -> List.fold_left ~f ~init lt
    | EBin (Cons, list_term, scal_term) -> f (eval_fold env fterm init list_term) scal_term
    | EBin (Concat, lterm, lterm') ->
        let lt1 = eval_fold env fterm init lterm in
        eval_fold env fterm lt1 lterm'
    | EIte (c, tlist1, tlist2) ->
        branch env c
          (fun () -> eval_fold env fterm init tlist1)
          (fun () -> eval_fold env fterm init tlist2)
    | e ->
        Log.error (fun f () -> pf f "⚠ Not a list: %a@." (box pp_term) (mk_term e));
        failwith "Cannot fold"
  in
  eval_term env t

let resources_of_symbs (tacc : typ) (sacc : symbolic_define) =
  let res_of_t typ t =
    match (typ, t.texpr) with TList _, EList elts -> RList elts | _, _ -> RScalar t
  in
  match (tacc, sacc.s_term.texpr) with
  | TTup types, ETuple elts -> (
      List.Or_unequal_lengths.(
        match List.map2 types elts ~f:res_of_t with Ok l -> l | Unequal_lengths -> failwith "TODO"))
  | TList _, EList elts -> [ RList elts ]
  | _, _ -> failwith "Expected type and symbolic expr do not match."

let resources_of_symb_list (ls : symbolic_define list) =
  let f sd =
    match sd.s_term.texpr with
    | EList elts -> RList elts
    | EStruct fields -> RList (List.map ~f:snd fields)
    | _ -> RScalar sd.s_term
  in
  List.map ~f ls

(**
   Unfold a function on arguments of type targs.
   Returns a result. If ok, returns an unfoldings_result.
   @Params : !Lang.Term.symb_lists_len.
*)

let func_unfoldings ?(name = "f") ?(min_unfoldings = 2) ~(conc_init : term) (f : term)
    (targs : typ list) : (unfoldings_result, Sexp.t) Result.t =
  let _ = conc_init in
  let _ = f in
  let tacc, telt =
    match targs with
    | [ tacc; telt ] -> (tacc, telt)
    | _ -> failwith "discover_for_func expected argst to be foldl type not: "
  in
  let mk_symb_state_and_list =
    (* TODO change how finitization works *)
    let solver = make_z3_solver () in
    let sacc, slist =
      let symb_accum = mk_symb_term ~name_hint:name tacc
      (* Create finite list of input symbols. *)
      and symb_list = mk_symb_term ~len:min_unfoldings (TList telt) in
      (symb_accum, symb_list)
    in
    declare_symb_define solver sacc;
    declare_symb_define solver slist;
    (sacc, slist, solver)
  in
  let calc_unfoldings (sacc, slist, solver) =
    match slist.s_term.texpr with
    | EList el ->
        let f (unfoldings, symb_state, conc_state) input =
          (* Try unfolding without branching first. *)
          let from_symb = branching_eval solver empty_env (mk_app f [ symb_state; input ])
          and from_init = branching_eval solver empty_env (mk_app f [ conc_state; input ]) in
          (* if !verbose then
             Log.progress (fun f inp -> Fmt.(pf f  "f(x) (+) %a" pp_term inp)) input; *)
          if !symbexe_verbose > 0 then
            Log.info (fun f () -> Fmt.(pf f "(Branching) Unfolding result: %a" pp_term from_symb));
          (unfoldings @ [ { input; from_symb; from_init } ], from_symb, from_init)
        in
        let unfoldings, _, _ = List.fold_left ~f ~init:([], sacc.s_term, conc_init) el in
        Ok
          {
            state_record_var = VarSet.singleton sacc.s_variable;
            init_as_resource = resources_of_symbs tacc sacc;
            unfoldings;
            solver;
            ret_type = [];
          }
    | _ ->
        Error
          Sexp.(
            List
              [
                Atom "Expected a list expression. Received ";
                sexp_of_term slist.s_term;
                Atom "Failed in unfoldings.";
              ])
  in
  (* Create the symbolic state and then compute the unfoldings. *)
  calc_unfoldings mk_symb_state_and_list

type eqns_unfolding_result = {
  zero_unfolding : unfolding IM.t;
  eqns_unfoldings : unfolding IM.t list;
  resources : resource list;
  solver : online_solver;
}

let eqns_unfoldings (func : l_eqns) : eqns_unfolding_result =
  let symb_vals, symb_l, solver =
    let solver = make_z3_solver () in
    let sacc, slist =
      let symbs =
        List.map
          ~f:(fun v -> (v.vid, mk_symb_term ~name_hint:v.vname v.vtype))
          (Set.to_list func.vars)
      (* Create finite list of input symbols. *)
      and symb_list = mk_symb_term ~len:3 (TList func.x.vtype) in
      (symbs, symb_list)
    in
    List.iter ~f:(fun symb -> declare_symb_define solver (snd symb)) sacc;
    declare_symb_define solver slist;
    (Map.of_alist_exn (module Int) sacc, slist, solver)
  in
  let resources = resources_of_symb_list (List.map ~f:snd (Map.to_alist symb_vals)) in
  let symbolic_start =
    Map.mapi
      ~f:(fun ~key ~data:sd ->
        {
          input = mk_empty_term;
          from_init = (Map.find_exn func.eqns key).einit;
          from_symb = sd.s_term;
        })
      symb_vals
  in
  let symbolic_list = match symb_l.s_term.texpr with EList el -> el | _ -> [] in
  let unfoldings =
    let oplus (l, last_u) symb_in =
      let env_from (sel : unfolding -> term) : env =
        {
          evars = func.vars $|| VarSet.singleton func.x;
          evals = Map.add_exn (Map.map ~f:sel last_u) ~key:func.x.vid ~data:symb_in;
        }
      in
      let fmap x =
        if has_nonlinear x.erhs && not !allow_nonlinear then
          { input = symb_in; from_init = x.erhs; from_symb = x.erhs }
        else
          {
            input = symb_in;
            from_init = branching_eval solver (env_from (fun eu -> eu.from_init)) x.erhs;
            from_symb = branching_eval solver (env_from (fun eu -> eu.from_symb)) x.erhs;
          }
      in
      (l @ [ last_u ], Map.map ~f:fmap func.eqns)
    in
    let x, y = List.fold ~init:([], symbolic_start) ~f:oplus symbolic_list in
    x @ [ y ]
  in
  match unfoldings with
  | hd :: tl -> { zero_unfolding = hd; eqns_unfoldings = tl; solver; resources }
  | [] -> { zero_unfolding = IM.empty; eqns_unfoldings = []; solver; resources }

type sfsp_unfolding_result = {
  zero_unfolding : unfolding;
  eqns_unfoldings : unfolding list;
  resources : resource list;
  solver : online_solver;
}

let pp_sfsp_unfolding_result (f : Formatter.t) (sur : sfsp_unfolding_result) : unit =
  Fmt.(
    pf f "@[<hov 2>u0 = %a@;ul = %a@]" (box pp_unfolding) sur.zero_unfolding
      (list ~sep:sp (box pp_unfolding))
      sur.eqns_unfoldings)

let start_state_len = ref 1

let start_list_len = ref 3

let reset () =
  start_state_len := 1;
  start_list_len := 4

let sfsp_unfoldings (func : std_soln) =
  let symb_start, symb_vals, symb_l, solver =
    let solver = make_z3_solver () in
    let sacc, slist =
      let symbs =
        match func.sf_ret with
        | TStruct (_, fields) ->
            let symbs =
              List.map
                ~f:(fun (fname, ftype) ->
                  (fname, mk_symb_term ~name_hint:fname ~len:!start_state_len ftype))
                fields
            in
            symbs
        | _ -> failwith "Apply Equations.std_soln_info before passing params."
      (* Create finite list of input symbols. *)
      and symb_list = mk_symb_term ~len:!start_list_len (fst func.sf_input).vtype in
      (symbs, symb_list)
    in
    List.iter ~f:(fun symb -> declare_symb_define solver (snd symb)) sacc;
    declare_symb_define solver slist;
    (mk_struct (List.map ~f:(fun (fname, sd) -> (fname, sd.s_term)) sacc), sacc, slist, solver)
  in
  let resources = resources_of_symb_list (List.map ~f:snd symb_vals) in
  let symbolic_list = match symb_l.s_term.texpr with EList el -> el | _ -> [] in
  let symbolic_start =
    { input = mk_empty_term; from_init = func.sf_init; from_symb = symb_start }
  in
  let a_var, s_var, f_oplus = oplus_of_soln func in
  let vars = VarSet.of_list [ a_var; s_var ] in
  let unfoldings =
    let oplus (l, last_u) symb_in =
      let env_from (sel : unfolding -> term) : env =
        {
          evars = vars;
          evals = Map.of_alist_exn (module Int) [ (a_var.vid, symb_in); (s_var.vid, sel last_u) ];
        }
      in
      let kap =
        let x =
          if !use_solver_eval then branching_eval solver (env_from (fun eu -> eu.from_init)) f_oplus
          else reduce_exn ~env:(env_from (fun eu -> eu.from_init)) f_oplus
        in
        let y =
          if !use_solver_eval then branching_eval solver (env_from (fun eu -> eu.from_symb)) f_oplus
          else reduce_exn ~env:(env_from (fun eu -> eu.from_symb)) f_oplus
        in
        { input = symb_in; from_init = x; from_symb = y }
      in
      (l @ [ last_u ], kap)
    in
    let x, y = List.fold ~init:([], symbolic_start) ~f:oplus symbolic_list in
    x @ [ y ]
  in
  if !start_state_len > !start_list_len then Int.incr start_state_len else Int.incr start_list_len;
  match unfoldings with
  | hd :: tl -> { zero_unfolding = hd; eqns_unfoldings = tl; solver; resources }
  | [] -> { zero_unfolding = symbolic_start; eqns_unfoldings = []; solver; resources }

let dependencies (f : term) (targs : typ list) (tres : typ) =
  let symb_tres = mk_var ~name:"symb" tres in
  let conc_init =
    match tres with
    | TTup tl -> mk_tuple (List.mapi ~f:(fun i _ -> mk_mem (mk_vt symb_tres) i) tl)
    | _ -> failwith "dependencies only on function returning tuples"
  in
  let from_one_unfolding unf =
    match unf with
    | [ unf0 ] -> (
        match unf0.from_init.texpr with
        | ETuple ets ->
            let f k elt =
              let all = Set.elements (Lang.Analyze.record_accesses_of elt) in
              let recs = List.filter ~f:(fun (v, _) -> Variable.(v = symb_tres)) all in
              (k, List.sort ~compare:Base.compare (List.map ~f:snd recs))
            in
            Ok (List.mapi ~f ets)
        | _ ->
            Error
              Sexp.(
                List
                  [
                    Atom "In dependencies, unfolding did not return tuple.";
                    sexp_of_term unf0.from_init;
                  ]))
    | _ ->
        Error
          Sexp.(
            List
              [ Atom "In dependencies, wrong number of unfoldings."; sexp_of_int (List.length unf) ])
  in
  match func_unfoldings ~name:"f" ~min_unfoldings:1 ~conc_init f targs with
  | Ok r -> from_one_unfolding r.unfoldings
  | Error s ->
      Fmt.(pf stdout "[ERROR] Error while unfolding to compute dependencies.");
      Error Sexp.(List [ Atom "In dependencies, error while unfolding."; s ])
