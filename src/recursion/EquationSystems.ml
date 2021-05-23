open Base
open Fmt
open Lang
open Lang.Analyze
open Lang.Term
open Lang.TermPp
open Lang.Typ
open Lang.SolutionDescriptors
open Lang.Unfold
open Solve.EquationSystemsSketches
open Utils

let from_loopbody (asserts : (VarSet.t * term) list) (t : term) =
  let coll = free_variables t in
  let xin, acc, lbody, linit, _ =
    match t.texpr with
    | EFoldL ({ texpr = ELambda ([ x; acc ], lbody); _ }, init, l)
    | EFoldR ({ texpr = ELambda ([ x; acc ], lbody); _ }, init, l) ->
        (x, acc, lbody, init, l)
    | _ -> failwith "Not a loop body."
  in
  let substs =
    match acc.vtype with
    | TStruct (s, fields) ->
        let f (fname, ft) =
          (fname, (mk_var ~not_fresh:true ~name:fname ft, mk_struct_mem ~s fname (mk_vt acc)))
        in
        List.map ~f fields
    | TTup _ -> failwith "TODO: eqnsystems from tuples"
    | _ -> [ (acc.vname, (acc, mk_vt acc)) ]
  in
  let apply_substs t =
    let f t (_, (v, st)) = replace_expr ~old:st ~by:(mk_vt v) t in
    List.fold ~init:t ~f substs
  in
  let x =
    let leqs, lins =
      match ((reduce_exn lbody).texpr, (reduce_exn linit).texpr) with
      | EStruct fields, EStruct ifields ->
          let f (fname, fterm) =
            let v =
              match List.Assoc.find substs ~equal:String.equal fname with
              | Some (v, _) -> v
              | None -> failwith "unexpected"
            in
            (v, apply_substs fterm)
          in
          (List.map ~f fields, List.map ~f ifields)
      | ETuple _, ETuple _ -> failwith "TODO; eqnsystems from tuples"
      | _ -> ([ (acc, lbody) ], [ (acc, linit) ])
    in
    List.fold2 ~init:(VarSet.empty, IM.empty) lins leqs
      ~f:(fun (vars, eqns) (v, _init) (v', _rhs) ->
        if not (v.vid = v'.vid) then failwith "unexpected"
        else
          let deps = Set.diff (free_variables _rhs) (coll $|| VarSet.singleton xin) in
          ( Set.add vars v,
            Map.add_exn eqns ~key:v.vid
              ~data:
                {
                  einit = _init;
                  erhs = AcTerm.(simplify_full (norm _rhs));
                  edeps = deps;
                  ejoin = Second _rhs;
                  elifts = VarSet.empty;
                } ))
  in
  let assumptions_on_input =
    let f (vs, t) = if Set.is_empty (Set.inter vs coll) then None else Some t in
    match List.filter_map ~f asserts with
    | [] -> None
    | [ t ] -> Some t
    | t1 :: t2 :: tl -> Some (mk_binop_of_list And t1 t2 tl)
  in

  match x with
  | Ok (vars, eqns) ->
      let s, fields = VarSet.to_struct vars in
      (* effectively declares *)
      let rstate = mk_var ~name:"$R" (TStruct (s, fields)) in
      let lstate = mk_var ~name:"$L" (TStruct (s, fields)) in
      make_deps_transitive
        {
          vars;
          x = xin;
          collection_inputs = coll;
          lstate;
          rstate;
          predicate = mk_empty_term;
          assume_input = assumptions_on_input;
          eqns;
          liftings = VarSet.empty;
          synt_time_lift = 0.;
          synt_time_join = 0.;
        }
  | _ -> failwith "Could not translate loop to function."

(* ============================================================================================= *)
(* ================================ OPTIMIZATIONS    =========================================== *)
(* ============================================================================================= *)

(* Variables that depend only on input or constant, or are using associative accumulators.
. *)
let solve_simple_joins (l : l_eqns) : l_eqns =
  let no_recdeps_vars l =
    let s, _ = VarSet.to_struct l.vars in
    let f var eqn =
      if Set.is_empty eqn.edeps then
        let other_deps = free_variables eqn.erhs in
        match Set.to_list other_deps with
        | [ _x ] when Variable.(_x = l.x) ->
            { eqn with ejoin = First (mk_struct_mem ~s var.vname (mk_vt l.rstate)) }
        | _ ->
            if Set.is_empty (Set.diff other_deps l.collection_inputs) then
              { eqn with ejoin = First (mk_vt var) }
            else eqn
      else
        match eqn.erhs.texpr with
        | EVar (Var v') when Variable.(v' = var) ->
            let a = Set.max_elt_exn l.collection_inputs in
            let new_init = if has_holes eqn.einit then mk_mem (mk_vt a) 0 else eqn.einit in
            {
              eqn with
              ejoin = First (mk_struct_mem ~s var.vname (mk_vt l.lstate));
              einit = new_init;
            }
        | EBin (op, { texpr = EVar (Var v'); _ }, tc) | EBin (op, tc, { texpr = EVar (Var v'); _ })
          ->
            if
              Variable.(v' = var)
              && Binop.is_ac op
              && Set.is_empty (Set.inter l.vars (free_variables tc))
            then
              let ejoin =
                let lvalue = mk_struct_mem ~s var.vname (mk_vt l.lstate) in
                let rvalue = mk_struct_mem ~s var.vname (mk_vt l.rstate) in
                mk_bin lvalue op rvalue
              in
              { eqn with ejoin = First ejoin }
            else eqn
        | _ -> eqn
    in

    { l with eqns = l_eqns_mapvar ~f l l.eqns }
  in
  no_recdeps_vars l

(* ============================================================================================= *)
(* ================================ PARSING RESPONSE =========================================== *)
(* ============================================================================================= *)

let parse_defs ?(only = None) (si : eqs_soln_info) (definitions : Sexp.t list) : eqs_soln_info =
  let define_op si opn body =
    let vars = VarSet.of_list [ si.func_info.lstate; si.func_info.rstate ] in
    match opn with
    | s when String.equal s si.join_name -> (
        let resp =
          try Solve.Rosette.parse_response vars body
          with e ->
            Log.error_msg Fmt.(str "Failed parsing %a." Sexp.pp_hum body);
            raise e
        in
        let t = subs_v_state si.func_info resp in
        match t.texpr with
        | EStruct fields ->
            {
              si with
              func_info = update_joins ~only si.func_info (fields_to_var si.func_info fields);
            }
        | _ ->
            Log.error (printer_msg "Expected a struct, but Rosette response is %a." rpp_term t);
            failwith "Unexpected response" )
    | s when String.equal s si.init_name -> (
        let resp = Solve.Rosette.parse_response si.func_info.collection_inputs body in
        let t = subs_v_state si.func_info resp in
        match t.texpr with
        | EStruct fields ->
            {
              si with
              func_info = update_inits ~only si.func_info (fields_to_var si.func_info fields);
            }
        | _ ->
            Log.error (printer_msg "Expected a struct, but Rosette response is %a." rpp_term t);
            failwith "Unexpected response" )
    | _ -> failwith "Unrecognized def in response."
  in
  let f si definition =
    match definition with
    | Sexp.(List [ Atom "define"; List (Atom opn :: _); body ]) -> define_op si opn body
    | Sexp.Atom "'" -> si
    | _ ->
        pf stdout "%a@." Sexp.pp_hum definition;
        failwith "not a def"
  in
  List.fold ~f ~init:si definitions

(* ============================================================================================= *)
(* ================================== INCREMENTAL SOLVING ====================================== *)
(* ============================================================================================= *)

let solve_step (func_name : string) (l : l_eqns) (v : variable list) : (int * l_eqns) option =
  Log.debug
    Fmt.(
      fun f () ->
        pf f "Search solution for @[%a@]."
          (list ~sep:comma (styled (`Fg `Blue) string))
          (List.map ~f:(fun v -> v.vname) v));
  let eq_sinfo =
    {
      func_name;
      join_name = "join_" ^ func_name;
      init_name = "init_" ^ func_name;
      tmp_file_sk =
        Utils.Naming.tmp_file
          (Fmt.str "join_%s_%s" func_name (List.hd_exn v).vname)
          Naming.ext_racket;
      tmp_file_out = Utils.Naming.tmp_file "join_output" "";
      func_info = l;
      sketching_level = 0;
    }
  in
  let sketch_infos =
    List.map
      ~f:(fun k ->
        {
          eq_sinfo with
          tmp_file_sk =
            Utils.Naming.tmp_file
              (Fmt.str "join_%s_%s" func_name (List.hd_exn v).vname)
              Naming.ext_racket;
          tmp_file_out = Caml.Filename.temp_file "join_output" "";
          sketching_level = k;
        })
      ListTools.(0 -- Config.num_parallel_processes)
  in
  let maybe_solns =
    Solve.Rosette.solve_sketches
      (compile_sketch ~select_fields:(Some (List.map ~f:(fun v -> v.vname) v)))
      (fun sk -> (sk.tmp_file_sk, sk.tmp_file_out))
      sketch_infos
  in
  let parsed_solns =
    let f (si, soln) =
      match soln with
      | [ Sexp.Atom "unsat" ] -> None
      | [ Sexp.Atom "sat" ] -> Some (true, si)
      | _ -> Some (false, parse_defs ~only:(Some v) si soln)
    in
    match maybe_solns with Some solns -> List.filter_map ~f solns | None -> []
  in
  let best_soln =
    match List.filter_map ~f:(fun (sat, si) -> if sat then Some si else None) parsed_solns with
    | si :: _ -> Some si
    | [] -> (
        match parsed_solns with
        | (_, si) :: _ -> Some si
        | [] ->
            Log.warning_msg (Fmt.str "No solution found for join of %a." (list pp_variable) v);
            None )
  in
  match best_soln with Some soln -> Some (soln.sketching_level, soln.func_info) | None -> None

let solve_by_var (l : l_eqns) : l_eqns option =
  let func_name = Lang.Alpha.get_new_name "f" in
  let l = solve_simple_joins l in
  Log.info (fun fmt () -> Fmt.pf fmt "Equation system:@;@[%a@]" pp_l_eqns l);
  let to_solve =
    let compare_f v1 v2 =
      match (Map.find l.eqns v1.vid, Map.find l.eqns v1.vid) with
      | Some eqn1, Some eqn2 ->
          let deps1 = eqn1.edeps in
          let deps2 = eqn2.edeps in
          if Set.mem deps2 v1 then -1
          else if Set.mem deps1 v2 then 1
          else compare (Set.length deps1) (Set.length deps2)
      | _, _ -> 1
    in
    let filter_f v =
      match Map.find l.eqns v.vid with
      | Some eqni -> ( match eqni.ejoin with Either.Second _ -> true | _ -> false )
      | None -> false
    in
    let all = List.sort ~compare:compare_f (List.filter ~f:filter_f (Set.elements l.vars)) in
    let bools, others =
      List.partition_tf all ~f:(fun v -> match v.vtype with TBool -> true | _ -> false)
    in
    List.map ~f:(fun v -> [ v ]) others @ [ bools ]
  in
  let f (b, accum) v =
    match v with
    | [] -> (true, accum)
    | _ -> (
        match solve_step func_name accum v with
        | Some (k, soln) ->
            Log.debug (fun formt () ->
                let ids = List.map ~f:Variable.id v in
                let current =
                  let eqns =
                    Map.to_alist (Map.filter_keys ~f:(fun i -> List.mem ~equal ids i) soln.eqns)
                  in
                  List.map
                    ~f:(fun (_, eqn) ->
                      match eqn.ejoin with Either.First j -> Some j | Either.Second _ -> None)
                    eqns
                in
                pf formt "@[Partial solution (k=%i):@;@[%a =@;%a@]@]" k
                  (list ~sep:comma pp_variable) v
                  (list ~sep:comma (parens (option pp_term)))
                  current);
            (b, soln)
        | None -> (false, accum) )
  in
  let solved, solution = List.fold ~f ~init:(true, l) to_solve in
  if solved then Some solution else None

let solve_direct (l : l_eqns) : l_eqns option =
  let func_name = Lang.Alpha.get_new_name "f" in
  let l' = solve_simple_joins l in
  let eq_sinfo =
    {
      func_name;
      join_name = "join_" ^ func_name;
      init_name = "init_" ^ func_name;
      tmp_file_sk = Utils.Naming.tmp_file "join_sketch" Naming.ext_racket;
      tmp_file_out = Utils.Naming.tmp_file "join_output" "";
      func_info = l';
      sketching_level = 0;
    }
  in
  let sketch_infos =
    List.map
      ~f:(fun k ->
        {
          eq_sinfo with
          tmp_file_sk = Utils.Naming.tmp_file "join_sketch" Naming.ext_racket;
          tmp_file_out = Caml.Filename.temp_file "join_output" "";
          sketching_level = k;
        })
      ListTools.(0 -- Config.num_parallel_processes)
  in
  let maybe_solns =
    Solve.Rosette.solve_sketches compile_sketch
      (fun sk -> (sk.tmp_file_sk, sk.tmp_file_out))
      sketch_infos
  in
  let parsed_solns =
    let f (si, soln) =
      match soln with
      | [ Sexp.Atom "unsat" ] -> None
      | [ Sexp.Atom "sat" ] -> Some (true, si)
      | _ -> Some (false, parse_defs si soln)
    in
    match maybe_solns with Some solns -> List.filter_map ~f solns | None -> []
  in
  let best_soln =
    match List.filter_map ~f:(fun (sat, si) -> if sat then Some si else None) parsed_solns with
    | si :: _ -> Some si
    | [] -> (
        match parsed_solns with
        | (_, si) :: _ -> Some si
        | [] ->
            Log.info (wrap "No solution found for this step.");
            None )
  in
  match best_soln with Some soln -> Some soln.func_info | None -> None

let solve_eqn_sys (l : l_eqns) = if !Config.break_problem then solve_by_var l else solve_direct l

let rec attempt_lift_and_solve ?(lift = !Config.default_lift) (l : l_eqns) =
  let (b, x), lift_time = timed (Discover.lift ~level:lift) l in
  match timed solve_eqn_sys { x with synt_time_lift = lift_time } with
  | Some x, join_time ->
      let x = { x with synt_time_join = x.synt_time_join +. join_time } in
      Log.info
        Fmt.(
          fun f () -> pf f "Solution found (in %.3f s):@;%a@." (lift_time +. join_time) pp_l_eqns x);
      Some x
  | None, join_time ->
      if b then
        attempt_lift_and_solve ~lift:(lift + 1)
          { l with synt_time_join = x.synt_time_join +. join_time }
      else None

let solve (asserts : (VarSet.t * term) list) (t : term) : l_eqns option =
  match attempt_lift_and_solve (from_loopbody asserts t) with
  | Some solution ->
      if !Config.dump_solutions then dump_eqns solution;
      Some solution
  | None -> None
