open Base
open Fmt
open Term
open AcTerm
open TermPp
open Typ
open Utils

type acc_op = { s : variable; a : variable; body : term }

type otimes_op = { s : variable; a : variable; e : variable; body : term }

type soln_info = {
  synt_time : float;
  tmp_file_sk : string;
  tmp_file_out : string;
  func_name : string;
  func_input : variable;
  func_input_assert : term option;
  func_body : term;
  return_type_as_set : bool;
  return_type : typ;
  target_func_name : string;
  target_accum_type : typ;
  list_field_name : string option;
  init : term;
  pre : acc_op;
  post : acc_op;
  otimes : otimes_op;
}

type std_soln = {
  sf_func : variable;
  sf_input : variable * term option;
  sf_as_set : bool;
  sf_ret : typ;
  sf_li : string;
  sf_init : term;
  sf_pre : acc_op;
  sf_post : acc_op;
  sf_otimes : otimes_op;
}

type div_soln = {
  synt_time : float;
  solved : bool;
  x : variable;
  pivots : (variable * (variable * variable list) * term) list;
  partitions : (variable * term) list;
}

type pred_soln = {
  synt_time : float;
  tmp_file_sk : string;
  tmp_file_out : string;
  base : std_soln;
  predicate : variable list * term;
  budget : ResourceModel.cbudget;
  divide : div_soln option; (* Is None when divide is arbitrary splitting. *)
}

type join_soln = {
  synt_time : float;
  pred_synt_time : float;
  tmp_file_sk : string;
  tmp_file_out : string;
  base : std_soln;
  predicate : variable list * term;
  budget : ResourceModel.cbudget;
  divide : div_soln option;
  join : variable list * term;
}

let std_acc_op (ao : acc_op) = { ao with body = AcTerm.simplify_easy (Unfold.reduce_exn ao.body) }

let std_otimes_op (oo : otimes_op) =
  { oo with body = AcTerm.simplify_easy (Unfold.reduce_exn oo.body) }

(* ============================================================================================= *)
(* ============================================================================================= *)

let term_of_div_soln (di : div_soln) : term =
  let partition_term =
    match di.partitions with
    | [ (_, body) ] -> mk_app (mk_vt _PARTITION_) [ body; mk_vt di.x ]
    | [ (_, body1); (_, body2) ] ->
        let x1, x2, x3 = (mk_var di.x.vtype, mk_var di.x.vtype, mk_var di.x.vtype) in
        mk_let_values [ x1; x2 ]
          (mk_app (mk_vt _PARTITION_) [ body1; mk_vt di.x ])
          (mk_let_values [ x2; x3 ]
             (mk_app (mk_vt _PARTITION_) [ body2; mk_vt x2 ])
             (mk_tuple [ mk_vt x1; mk_vt x2; mk_vt x3 ]))
    | _ -> failwith "TODO; only 3 partitions supported for now"
  in
  let rec t_pivots l =
    match l with
    | [] -> partition_term
    | (pivot_v, pivot_term) :: tl -> mk_let (Var pivot_v) pivot_term (t_pivots tl)
  in
  let pivot_v = List.map ~f:(fun (v, _, t) -> (v, t)) di.pivots in
  t_pivots pivot_v

let get_pivots divide = List.map ~f:(fun (v, _, _) -> v) divide.pivots

(* ============================================================================================= *)
(* ============================================================================================= *)

let check_std_soln (st : std_soln) =
  assert (Variable.(st.sf_post.a = st.sf_pre.a));
  assert (Variable.(st.sf_pre.a = st.sf_otimes.a));
  match
    (type_of st.sf_init, type_of st.sf_otimes.body, type_of st.sf_post.body, type_of st.sf_pre.body)
  with
  | Ok ti, Ok totimes, Ok tpost, Ok tpre ->
      ETypes.(
        assert (Structs.is_struct_type ti);
        assert (ti = st.sf_ret);
        assert (ti = st.sf_pre.s.vtype);
        assert (tpre = st.sf_otimes.s.vtype);
        assert (totimes = st.sf_otimes.s.vtype);
        assert (tpre = st.sf_post.s.vtype);
        assert (tpost = ti))
  | _ -> assert false

let reduce_si (si : soln_info) (t : typ) =
  let func_v = mk_var ~name:si.func_name (TFun (si.func_input.vtype, t)) in
  {
    sf_func = func_v;
    sf_input = (si.func_input, si.func_input_assert);
    sf_as_set = si.return_type_as_set;
    sf_li = (match si.list_field_name with Some x -> x | None -> failwith "1:Unexpected");
    sf_ret = t;
    sf_init = AcTerm.simplify_easy (Unfold.reduce_exn si.init);
    sf_pre = std_acc_op si.pre;
    sf_post = std_acc_op si.post;
    sf_otimes = std_otimes_op si.otimes;
  }

let transform_to_struct (si : soln_info) (t : typ) =
  let field = match si.list_field_name with None -> Alpha.get_new_name "l" | Some n -> n in
  let new_sname = Structs.decl_of_vars [ (field, t) ] in
  let new_t = TStruct (new_sname, [ (field, t) ]) in
  let updated_pre =
    assert (ETypes.(si.pre.s.vtype = t));
    let new_s = mk_var ~name:si.pre.s.vname new_t in
    let new_b = replace_expr ~old:(mk_vt si.pre.s) ~by:(mk_vt new_s) si.pre.body in
    { s = new_s; body = new_b; a = si.pre.a }
  in
  let update_post = { si.post with body = mk_struct [ (field, si.post.body) ] } in
  ( new_t,
    {
      si with
      list_field_name = Some field;
      init = mk_struct [ (field, si.init) ];
      pre = updated_pre;
      post = update_post;
      return_type = new_t;
    } )

let std_soln_info (si : soln_info) =
  let t =
    match type_of si.init with
    | Ok t -> t
    | _ ->
        Log.error (printer_msg "Return type: %a." pp_typ si.return_type);
        failwith "Failed to check well-formedness of input"
  in
  let new_si =
    match t with
    | TStruct _ -> reduce_si si t
    | _ ->
        let t', si' = transform_to_struct si t in
        reduce_si si' t'
  in
  check_std_soln new_si;
  new_si

let oplus_of_soln (soln : std_soln) : variable * variable * term =
  let struct_name = match soln.sf_ret with TStruct (s, _) -> s | _ -> failwith "2:Unexpected" in
  let f_post = mk_lambda [ soln.sf_post.a; soln.sf_post.s ] soln.sf_post.body in
  let f_pre = mk_lambda [ soln.sf_pre.a; soln.sf_pre.s ] soln.sf_pre.body in
  let f_otimes = mk_lambda [ soln.sf_otimes.e; soln.sf_otimes.s ] soln.sf_otimes.body in
  let s = mk_var soln.sf_ret in
  let a = soln.sf_pre.a in
  let f_oplus_body =
    mk_app f_post
      [
        mk_vt a;
        mk_foldl ~f:f_otimes
          ~init:(mk_app f_pre [ mk_vt a; mk_vt s ])
          (mk_struct_mem ~s:struct_name soln.sf_li (mk_vt s));
      ]
  in
  (soln.sf_pre.a, s, f_oplus_body)

let pp_soln_info_func (fmt : Formatter.t) (si : soln_info) =
  let pp0 fmt () =
    match si.func_input_assert with
    | Some t ->
        let fv = Analyze.free_variables t in
        pf fmt "@[assert forall %a in input, %a)@]" VarSet.pp_var_names fv pp_term t
    | None -> ()
  in
  let pp1 fmt () =
    pf fmt "@[%a %a = foldl ⊕ %a %a @]"
      (styled `Italic string)
      si.target_func_name pp_variable si.func_input (box pp_term) si.init pp_variable si.func_input
  in
  let pp2 fmt () =
    match (si.target_accum_type, si.list_field_name) with
    | TStruct (_, _), Some lfn ->
        pf fmt "@[<hov 2>s ⊕ a =@;(%a (foldl (λ e s.(a, s) ⊗ e)) (%a s a) s.%s) a))"
          (styled `Bold string)
          "post"
          (styled `Bold string)
          "pre" lfn
    | TList _, None ->
        pf fmt "@[<hov 2>s ⊕ a =@;(%a (foldl (λ e s.(a, s) ⊗ e)) (%a s a) s) a))"
          (styled `Bold string)
          "post"
          (styled `Bold string)
          "pre"
    | _ -> ()
  in
  let pp3 fmt () =
    pf fmt "@[<v 2>(%s, %s) ⊗ %s =@;%a)@]" si.otimes.a.vname si.otimes.s.vname si.otimes.e.vname
      (box pp_term) si.otimes.body
  in
  let pp4 fmt () =
    pf fmt "@[<v 2>%a %s %s =@;%a@]"
      (styled `Bold string)
      "post" si.post.s.vname si.post.a.vname (box pp_term) si.post.body
  in
  let pp5 fmt () =
    pf fmt "@[<v 2>%a %s %s = @;%a@]"
      (styled `Bold string)
      "pre" si.pre.s.vname si.pre.a.vname (box pp_term) si.pre.body
  in
  pf fmt "@[%a@]@;@[%a@]@;@[%a@]@;@[%a@]@;@[%a@]@;@[%a@]" pp0 () pp1 () pp2 () pp3 () pp4 () pp5 ()

let pp_std_soln_func (fmt : Formatter.t) (si : std_soln) =
  let pp1 fmt () =
    pf fmt "@[%a %a = List.fold ~f:⊕ ~init:%a %a @]"
      (styled `Italic string)
      si.sf_func.vname pp_variable (fst si.sf_input) (box pp_term) si.sf_init pp_variable
      (fst si.sf_input)
  in
  let pp2 fmt () =
    match (si.sf_ret, si.sf_li) with
    | TStruct (_, _), lfn ->
        pf fmt
          "@[<hov 2>s ⊕ a =@;(%a (List.fold ~f:(λ e s.(a, s) ⊗ e)) ~init:(%a s a) s.%s) a))@]"
          (styled `Bold string)
          "post"
          (styled `Bold string)
          "pre" lfn
    | _ -> ()
  in
  let pp3 fmt () =
    pf fmt "@[<v 2>(%s, %s) ⊗ %s =@;%a)@]" si.sf_otimes.a.vname si.sf_otimes.s.vname
      si.sf_otimes.e.vname (box pp_term) si.sf_otimes.body
  in
  let pp4 fmt () =
    pf fmt "@[<v 2>%a %s %s =@;%a@]"
      (styled `Bold string)
      "post" si.sf_post.s.vname si.sf_post.a.vname (box pp_term) si.sf_post.body
  in
  let pp5 fmt () =
    pf fmt "@[<v 2>%a %s %s = @;%a@]"
      (styled `Bold string)
      "pre" si.sf_pre.s.vname si.sf_pre.a.vname (box pp_term) si.sf_pre.body
  in
  pf fmt "‣ @[%a@]@;‣ @[%a@]@;where@;‣ @[%a@]@;‣ @[%a@]@;‣ @[%a@]" pp1 () pp2 () pp3 ()
    pp4 () pp5 ()

(* ================================================================================================= *)

let add_join_to_pred_soln (pi : pred_soln) (ji : variable list * term) : join_soln =
  let joi_sk, joi_out =
    let budget = pi.budget in
    let bs = Fmt.str "_%i_%i_%i_" budget.k budget.m budget.c in
    ( Utils.Naming.tmp_file ("join_sketch" ^ bs) Naming.ext_racket,
      Caml.Filename.temp_file ("join_output" ^ bs) "" )
  in
  {
    synt_time = 0.0;
    pred_synt_time = pi.synt_time;
    tmp_file_sk = joi_sk;
    tmp_file_out = joi_out;
    base = pi.base;
    join = ji;
    predicate = pi.predicate;
    divide = pi.divide;
    budget = pi.budget;
  }

let add_div_synt_times div_time : pred_soln list -> pred_soln list =
  List.map ~f:(fun (d : pred_soln) ->
      match d.divide with
      | Some div -> { d with divide = Some { div with synt_time = div.synt_time +. div_time } }
      | None -> { d with divide = None })

let pp_join_soln (fmt : Formatter.t) (ji : join_soln) =
  pf fmt "%a@;%a@.@."
    (styled `Underline string)
    "Single pass function:" (box pp_std_soln_func) ji.base;
  if !Log.verbose then
    pf fmt "%a@;@[P(%a) = @] %a@.@."
      (styled `Underline string)
      (Fmt.str "Predicate (%.3f s):" ji.pred_synt_time)
      (list ~sep:comma pp_variable) (fst ji.predicate) (box pp_term) (snd ji.predicate);
  ( match ji.divide with
  | Some d ->
      let div_term = term_of_div_soln d in
      pf fmt "%a@;@[divide(%s) =@;%a@]@.@."
        (styled `Underline string)
        (Fmt.str "Divide function (%4.2fs):" d.synt_time)
        d.x.vname (box pp_term) div_term
  | None -> () );
  match fst ji.join with
  | [ a; b ] ->
      pf fmt "@[%a@;@[join(%s, %s) =@;%a@]@]@."
        (styled `Underline string)
        (Fmt.str "Join (%4.2f s):" ji.synt_time)
        a.vname b.vname (box pp_term) (snd ji.join)
  | l ->
      pf fmt "@[%a@;@[join(%a)=@;%a@]@]@."
        (styled `Underline string)
        (Fmt.str "Join (%4.2f s):" ji.synt_time)
        (list ~sep:comma pp_variable) l (box pp_term) (snd ji.join)

let dump_id = ref 0

let dump_join_soln (ji : join_soln) : unit =
  let out_filename =
    let fn = Caml.Filename.basename (Caml.Filename.remove_extension !Config.master_file) in
    Fmt.str "%s_%i-%i-%i_%i_soln.txt" fn ji.budget.k ji.budget.m ji.budget.c !dump_id
  in
  Int.incr dump_id;
  let oc = Stdio.Out_channel.create out_filename in
  let fout = Stdlib.Format.formatter_of_out_channel oc in
  pp_join_soln fout ji;
  Log.success_msg Fmt.(str "Solution in %s" out_filename);
  Stdio.Out_channel.close oc

(* ================================================================================================= *)
(* ================================= For single loops (no budget) ================================== *)
(* ================================================================================================= *)

type eqn_info = {
  erhs : term;
  einit : term;
  edeps : VarSet.t;
  ejoin : (term, term) Either.t;
  elifts : VarSet.t;
}

let pp_eqn_info formt eqn =
  let j = match eqn.ejoin with Either.First j -> j | Either.Second j -> j in
  Fmt.(
    pf formt "@[RHS :@;%a@]@;@[INIT :@;%a@]@[JOIN :%a@]@;" pp_term eqn.erhs pp_term eqn.einit
      pp_term j)

type l_eqns = {
  eqns : eqn_info IM.t;
  vars : VarSet.t;
  lstate : variable;
  rstate : variable;
  x : variable;
  collection_inputs : VarSet.t;
  predicate : term;
  assume_input : term option;
  liftings : VarSet.t;
  synt_time_lift : float;
  synt_time_join : float;
}

type eqs_soln_info = {
  tmp_file_sk : string;
  tmp_file_out : string;
  join_name : string;
  init_name : string;
  func_name : string;
  func_info : l_eqns;
  sketching_level : int;
}

let _struct_creation_helper (vs : VarSet.t) =
  let sname, sfields = VarSet.to_struct vs in
  let st = TStruct (sname, sfields) in
  let lstate = mk_var ~name:"$L" st in
  let rstate = mk_var ~name:"$R" st in
  (sname, sfields, lstate, rstate)

let _update_structs ?(addressing = identity) ?(forget = []) ~(old : l_eqns) ~(new_l : variable)
    ~(new_r : variable) (new_s : string) (j : term) =
  let sname, sfields = VarSet.to_struct old.vars in
  let substitute x =
    let substs =
      List.concat_map
        ~f:(fun (field, _) ->
          if List.mem forget ~equal:String.equal field then []
          else
            [
              ( mk_struct_mem ~s:sname field (mk_vt old.rstate),
                mk_struct_mem ~s:new_s (addressing field) (mk_vt new_r) );
              ( mk_struct_mem ~s:sname field (mk_vt old.lstate),
                mk_struct_mem ~s:new_s (addressing field) (mk_vt new_l) );
            ])
        sfields
    in
    TermUtils.apply_substs substs x
  in
  substitute j

let get_struct_name func =
  match func.lstate.vtype with TStruct (s, _) -> s | _ -> failwith "SHould be a struct."

let get_init func vid = match Map.find func.eqns vid with Some eqn -> Some eqn.einit | _ -> None

let get_rhs func vid = match Map.find func.eqns vid with Some eqn -> Some eqn.erhs | _ -> None

let get_join func vid =
  match Map.find func.eqns vid with
  | Some eqn -> ( match eqn.ejoin with First solved -> Some solved | _ -> None )
  | _ -> None

(* Dependencies *)
let get_deps leqns v = Option.map ~f:(fun e -> e.edeps) (Map.find leqns.eqns v.vid)

let get_deps_i leqns i = Option.map ~f:(fun e -> e.edeps) (Map.find leqns.eqns i)

let get_var leqns vid = VarSet.find_by_id leqns.vars vid

let eqn_same_deps eqn1 eqn2 = Set.equal eqn1.edeps eqn2.edeps

let make_deps_transitive (leqns : l_eqns) : l_eqns =
  let rec aux leqns =
    let fmap eqn =
      let i_deps = eqn.edeps in
      let new_deps =
        List.fold ~init:i_deps
          ~f:(fun s d -> match d with Some s' -> s $|| s' | None -> s)
          (List.map ~f:(get_deps leqns) (Set.elements i_deps))
      in
      { eqn with edeps = new_deps }
    in
    let new_map = Map.map ~f:fmap leqns.eqns in
    let new_leqns = { leqns with eqns = new_map } in
    if Map.equal eqn_same_deps new_map leqns.eqns then new_leqns else aux new_leqns
  in
  aux leqns

let is_indirect_dep (func : l_eqns) (eqn : eqn_info) (vs : VarSet.t) =
  let match_rhs_term t =
    match
      Map.max_elt
        (Map.filter func.eqns ~f:(fun eqn' ->
             Terms.(eqn'.erhs = t) && not Terms.(eqn'.erhs = eqn.erhs)))
    with
    | Some (vid, _) -> VarSet.find_by_id func.vars vid
    | _ -> None
  in
  let pure_term () =
    let trf _ t = Option.map ~f:mk_vt (match_rhs_term t) in
    Transform.transform trf eqn.erhs
  in
  let res =
    match eqn.erhs.texpr with
    | EBin ((Max | Min), _, _) ->
        Set.is_empty (Set.inter vs (Analyze.free_variables (pure_term ())))
    | _ -> false
  in
  res

(* Lifting information *)
let get_lifts leqns v = Option.map ~f:(fun e -> e.elifts) (Map.find leqns.eqns v.vid)

let get_lifts_i leqns i = Option.map ~f:(fun e -> e.elifts) (Map.find leqns.eqns i)

let eqn_same_lifts eqn1 eqn2 = Set.equal eqn1.elifts eqn2.elifts

let make_lifts_transitive (leqns : l_eqns) : l_eqns =
  let rec aux leqns =
    let fmap eqn =
      let new_lifts =
        List.fold ~init:eqn.elifts
          ~f:(fun s d -> match d with Some s' -> s $|| s' | None -> s)
          (List.map ~f:(get_lifts leqns) (Set.elements eqn.edeps))
      in
      { eqn with elifts = new_lifts }
    in
    let new_map = Map.map ~f:fmap leqns.eqns in
    let new_leqns = { leqns with eqns = new_map } in
    if Map.equal eqn_same_lifts new_map leqns.eqns then new_leqns else aux new_leqns
  in
  aux leqns

let update_deps (leqns : l_eqns) : l_eqns =
  let f eqn = { eqn with edeps = Set.inter leqns.vars (Analyze.free_variables eqn.erhs) } in
  make_lifts_transitive (make_deps_transitive { leqns with eqns = Map.map ~f leqns.eqns })

let update_struct_vars (new_vars : VarSet.t) (l : l_eqns) =
  let new_sname, _, new_lstate, new_rstate = _struct_creation_helper new_vars in
  let forget = VarSet.names (Set.diff l.vars new_vars) in
  let update t = _update_structs ~old:l ~forget ~new_l:new_lstate ~new_r:new_rstate new_sname t in
  let neqns =
    let f eqn =
      {
        erhs = update eqn.erhs;
        ejoin = Either.map ~first:update ~second:update eqn.ejoin;
        einit = update eqn.einit;
        elifts = Set.inter eqn.elifts new_vars;
        edeps = Set.inter eqn.elifts new_vars;
      }
    in
    Map.map ~f l.eqns
  in
  { l with vars = new_vars; eqns = neqns; lstate = new_lstate; rstate = new_rstate }

let subs_state_v ?(state = None) (func_info : l_eqns) (t : term) : term =
  let stv = match state with None -> func_info.lstate | Some v -> v in
  let s, fields = VarSet.to_struct func_info.vars in
  let id_fields =
    List.map2_exn ~f:(fun v field -> (v, field)) (Set.to_list func_info.vars) fields
  in
  let f accum (v, (field, _)) =
    replace_expr ~old:(mk_vt v) ~by:(mk_struct_mem ~s field (mk_vt stv)) accum
  in
  List.fold ~f ~init:t id_fields

let subs_rstate_v (func : l_eqns) (t : term) : term =
  let stv = func.rstate in
  let s, fields = VarSet.to_struct func.vars in
  let id_fields = List.map2_exn ~f:(fun v field -> (v, field)) (Set.to_list func.vars) fields in
  let f accum (v, (field, _)) =
    replace_expr ~by:(mk_vt v) ~old:(mk_struct_mem ~s field (mk_vt stv)) accum
  in
  List.fold ~f ~init:t id_fields

let subs_v_state (func_info : l_eqns) (t : term) : term =
  let stv = func_info.lstate in
  let s, fields = VarSet.to_struct func_info.vars in
  let id_fields =
    List.map2_exn ~f:(fun v field -> (v, field)) (Set.to_list func_info.vars) fields
  in
  let f accum (v, (field, _)) =
    replace_expr ~old:(mk_struct_mem ~s field (mk_vt stv)) ~by:(mk_vt v) accum
  in
  List.fold ~f ~init:t id_fields

let l_eqns_mapvar (l : l_eqns) map ~f =
  Map.mapi map ~f:(fun ~key ~data ->
      let v = VarSet.find_by_id l.vars key in
      match v with Some var -> f var data | _ -> failwith "Malformed leqns")

let fields_to_var (l : l_eqns) (fields : (string * 'a) list) =
  let f accum (fn, x) =
    match VarSet.find_by_name l.vars fn with
    | Some v -> Map.add_exn accum ~key:v.vid ~data:x
    | None -> accum
  in
  List.fold ~f ~init:IM.empty fields

let update_joins ?(only = None) (l : l_eqns) (join_solutions : term IM.t) =
  let n_eqs =
    let update key data =
      match Map.find join_solutions key with
      | Some j -> { data with ejoin = Either.First (AcTerm.simplify_full j) }
      | None -> data
    in
    let f ~key ~(data : eqn_info) =
      match only with
      | Some key' -> if List.exists key' ~f:(fun v -> v.vid = key) then update key data else data
      | None -> update key data
    in
    Map.mapi ~f l.eqns
  in
  { l with eqns = n_eqs }

let update_inits ?(only = None) (l : l_eqns) (init_solutions : term IM.t) =
  let n_eqs =
    let update key data =
      match Map.find init_solutions key with Some j -> { data with einit = j } | None -> data
    in
    let f ~key ~(data : eqn_info) =
      match only with
      | Some key' -> if List.exists key' ~f:(fun v -> v.vid = key) then update key data else data
      | None -> update key data
    in
    Map.mapi ~f l.eqns
  in
  { l with eqns = n_eqs }

let collect_conditionals (l : l_eqns) =
  let f ~key:_ ~data:eqn es =
    let conds = Analyze.get_conditions eqn.erhs in
    Set.union es conds
  in
  Map.fold ~f ~init:(Set.empty (module Terms)) l.eqns

let collect_positive_conditionals (l : l_eqns) =
  let single = Set.singleton (module Terms) in
  let trf trec t =
    match t.texpr with
    | EIte (c, tt, tf) ->
        let c' =
          if is_constant tt || is_var tt then Some c
          else if is_constant tf || is_var tf then Some (mk_not c)
          else None
        in
        Option.map ~f:(fun c -> if has_branching c then trec c else single c) c'
    | _ -> None
  in
  let _transf =
    Transform.recurse { join = Set.union; init = Set.empty (module Terms); case = trf }
  in
  let f ~key:_ ~data:eqn es =
    let rhs = simplify_full (Normalize.normalize eqn.erhs) in
    let conds = _transf rhs in
    Set.union es conds
  in
  Set.elements (Map.fold ~f ~init:(Set.empty (module Terms)) l.eqns)

let maybe_to_lift (l : l_eqns) : VarSet.t =
  let ids =
    Map.filter
      ~f:(fun eqn ->
        is_int eqn.erhs
        &&
        match eqn.ejoin with
        | Either.First _ -> false
        | Either.Second _ -> has_branching eqn.erhs && not (has_nonlinear eqn.erhs))
      l.eqns
  in
  let ids = ListTools.lfst (Map.to_alist ids) in
  Set.filter ~f:(fun v -> List.mem ids ~equal v.vid) l.vars

let unsolved (l : l_eqns) : VarSet.t =
  let ids =
    Map.filter
      ~f:(fun eqn -> match eqn.ejoin with Either.First _ -> false | Either.Second _ -> true)
      l.eqns
  in
  let ids = ListTools.lfst (Map.to_alist ids) in
  Set.filter ~f:(fun v -> List.mem ids ~equal v.vid) l.vars

let apply_subs_to_eqn subs eqn =
  let tsubs = List.map ~f:(fun (v1, v2) -> (mk_vt v1, v2)) subs in
  let vsubs =
    List.concat_map
      ~f:(fun (v1, v2) -> match v2.texpr with EVar (Var v) -> [ (v1, v) ] | _ -> [])
      subs
  in
  let update t = apply_substs_ac tsubs t in
  {
    erhs = simplify_full (update eqn.erhs);
    ejoin = Either.map ~first:update ~second:update eqn.ejoin;
    einit = simplify_full (update eqn.einit);
    elifts = VarSet.substitute vsubs eqn.elifts;
    edeps = VarSet.substitute vsubs eqn.edeps;
  }

let same_equation ((v1, eqn1) : variable * eqn_info) ((v2, eqn2) : variable * eqn_info) : bool =
  if ACES.(eqn1.einit = eqn2.einit) then
    let pholder = mk_var v2.vtype in
    let e2rhs = replace_expr ~old:(mk_vt v2) ~by:(mk_vt pholder) eqn2.erhs in
    let e1rhs = replace_expr ~old:(mk_vt v1) ~by:(mk_vt pholder) eqn1.erhs in
    ACES.(e1rhs = e2rhs)
  else false

let constant_function func ((v, eqn) : variable * eqn_info) : (variable * term) option =
  match (eqn.einit.texpr, eqn.erhs.texpr) with
  | EConst (CBool false), EBin (And, { texpr = EVar (Var v'); _ }, _)
  | EConst (CBool false), EBin (And, _, { texpr = EVar (Var v'); _ }) ->
      if Variable.(v' = v) then Some (v, mk_false) else None
  | EConst (CBool true), EBin (Or, { texpr = EVar (Var v'); _ }, _)
  | EConst (CBool true), EBin (Or, _, { texpr = EVar (Var v'); _ }) ->
      if Variable.(v' = v) then Some (v, mk_true) else None
  | _, EBin (And, { texpr = EVar (Var v'); _ }, { texpr = EVar (Var v''); _ }) -> (
      let var' = if Variable.(v' = v) then v'' else v' in
      match get_init func var'.vid with
      | Some { texpr = EConst (CBool false); _ } -> Some (v, mk_false)
      | _ -> None )
  | _, EBin (Or, { texpr = EVar (Var v'); _ }, { texpr = EVar (Var v''); _ }) -> (
      let var' = if Variable.(v' = v) then v'' else v' in
      match get_init func var'.vid with
      | Some { texpr = EConst (CBool true); _ } -> Some (v, mk_false)
      | _ -> None )
  | EConst _, EVar (Var v') when Variable.(v' = v) -> Some (v, eqn.einit)
  | _ -> None

let pre_clean_l_eqns (leq : l_eqns) : l_eqns =
  let equations =
    List.filter_map
      ~f:(fun (vid, eqni) -> Option.map ~f:(fun v -> (v, eqni)) (VarSet.find_by_id leq.vars vid))
      (Map.to_alist ~key_order:`Increasing leq.eqns)
  in
  let eqns', _ =
    let f (new_eqns, subs) ((v1, eqn) : variable * eqn_info) =
      let eqn' = apply_subs_to_eqn subs eqn in
      match List.find new_eqns ~f:(fun a -> same_equation a (v1, eqn')) with
      | Some (v1', _) ->
          let new_subs = subs @ [ (v1, mk_vt v1') ] in
          (List.map ~f:(fun (v, e) -> (v, apply_subs_to_eqn new_subs e)) new_eqns, new_subs)
      | None -> (
          match constant_function leq (v1, eqn') with
          | Some sub -> (new_eqns, subs @ [ sub ])
          | None -> (new_eqns @ [ (v1, eqn') ], subs) )
    in
    List.fold ~f ~init:([], []) equations
  in
  let new_vars = VarSet.of_list (ListTools.lfst eqns') in
  let new_eqns = Map.of_alist_exn (module Int) (List.map ~f:(fun (v, e) -> (v.vid, e)) eqns') in
  if Map.length new_eqns < Map.length leq.eqns then
    update_struct_vars new_vars { leq with eqns = new_eqns }
  else leq

let clean_l_eqns (leq : l_eqns) =
  let rec aux i leq =
    let leq' = pre_clean_l_eqns leq in
    if (not (Map.length leq'.eqns = Map.length leq.eqns)) && i < 100 then aux (i + 1) leq' else leq'
  in
  aux 0 leq

let post_clean_l_eqns (func : l_eqns) (orig : VarSet.t) =
  let aux varset func =
    let f vs var =
      match (get_rhs func var.vid, get_join func var.vid) with
      | Some erhs, Some ejoin ->
          let ejoin' = subs_rstate_v func ejoin in
          let newv = Analyze.(free_variables erhs $|| free_variables ejoin') in
          vs $|| newv
      | _ -> vs
    in
    List.fold_left ~init:varset ~f (Set.elements varset)
  in
  let rec fixp vs =
    let vs' = aux vs func in
    if Set.equal vs vs' then vs else fixp vs'
  in
  fixp orig

let pp_l_eqns (f : Formatter.t) (leq : l_eqns) =
  let sf = subs_state_v leq in
  let s1 = mk_var leq.lstate.vtype ~name:"_s1" in
  let eq_sep fmt () = pf fmt " =@;" in
  let inits =
    List.map
      ~f:(fun (vid, t) ->
        match get_var leq vid with Some v -> (v.vname, t.einit) | None -> ("??", t.einit))
      (Map.to_alist leq.eqns)
  in
  let rhs =
    List.map
      ~f:(fun (vid, t) ->
        match get_var leq vid with
        | Some v -> (v.vname, subs_state_v ~state:(Some s1) leq t.erhs)
        | None -> ("??", t.einit))
      (Map.to_alist leq.eqns)
  in
  let joins =
    List.map
      ~f:(fun (vid, t) ->
        match (get_var leq vid, t.ejoin) with
        | Some v, First j -> (v.vname, sf j)
        | _ -> ("??", mk_empty_term))
      (Map.to_alist leq.eqns)
  in
  pf f "@.// --- Lifted function ---@.";
  (* Initialization. *)
  pf f "@[<hov 2>%a =@;{@;@[%a;@]@;}@]" pp_variable s1
    (list ~sep:semicolon (pair ~sep:eq_sep string pp_term))
    inits;
  (* Loop body. *)
  pf f "@[<v 2>for(%s in %a){@;@[<v 2>%a = {@;@[<v>%a@];@]@;}@;}@;return %a;@]@." leq.x.vname
    VarSet.pp_var_names leq.collection_inputs pp_variable s1
    (list ~sep:semicolon (box (pair ~sep:eq_sep string pp_term)))
    rhs pp_variable s1;
  (* Splitting predicate. *)
  pf f "@[//--- Splitting predicate:@;%a@]@." pp_term leq.predicate;
  pf f "//--- Join function ---@.";
  pf f "@[<hov 2>join(%a,%a) = {@;@[<v>%a;@]@]@;}@." pp_variable leq.lstate pp_variable leq.rstate
    (list ~sep:semicolon (box (pair ~sep:eq_sep string pp_term)))
    joins;
  pf f "// Synthesized in (predicate : %.2f s) + (join : %.2f s)@." leq.synt_time_lift
    leq.synt_time_join

let pp_eqn f (v, t) = pf f "@[%s@;=@;%a@]" v.vname rpp_term t

let dump_eqns (func : l_eqns) : unit =
  let out_filename =
    let fn = Caml.Filename.basename (Caml.Filename.remove_extension !Config.master_file) in
    Fmt.str "%s_0-2-2_%i_soln.txt" fn !dump_id
  in
  Int.incr dump_id;
  let oc = Stdio.Out_channel.create out_filename in
  let fout = Stdlib.Format.formatter_of_out_channel oc in
  pp_l_eqns fout func;
  Log.success_msg Fmt.(str "Solution in %s" out_filename);
  Stdio.Out_channel.close oc
