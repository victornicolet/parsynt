open Base
open Lang.Term
open Lang.AcTerm
open Lang.Analyze
open Lang.TermPp
open Lang.Typ
open Lang.SolutionDescriptors
open Option.Let_syntax

let make_base_choice_of_var (x : variable) =
  match x.vtype with
  | TInt -> mk_vt x
  | TBool -> mk_vt x
  | TStruct (s, fields) -> (
      let choices = List.map fields ~f:(fun (fname, _) -> mk_struct_mem ~s fname (mk_vt x)) in
      match mk_choice choices with
      | Ok c -> c
      | Error _ -> failwith Fmt.(str "Could not make choice of %a" (list pp_term) choices) )
  | _ -> failwith (Fmt.str "Unsupported type to make base choices on: %a" pp_typ x.vtype)

let nonzero_op op = match op with Mod | Div -> true | _ -> false

let choice_and_or =
  match mk_choice [ mk_vt Binop.ac_or; mk_vt Binop.ac_and ] with
  | Ok c -> c
  | _ -> failwith "Unexpected"

let choice_int_op =
  match mk_choice [ mk_vt Binop.ac_plus; mk_vt Binop.ac_max; mk_vt Binop.ac_min ] with
  | Ok c -> c
  | _ -> failwith "Unexpected"

let emptychecks ?(with_base_c = false) ts =
  let lists = List.filter ~f:(fun t -> match t.ttyp with TList _ -> true | _ -> false) ts in
  match lists with
  | [] -> []
  | _ ->
      [
        mk_choice_exn
          ( List.map ~f:(fun lt -> mk_un (UChoice [ Id; Not ]) (mk_un IsEmpty lt)) lists
          @ if with_base_c then [ mk_true; mk_false ] else [] );
      ]

let bool_choice ?(no_eq = false) ?(purefunc = false) k ts =
  let bools = List.filter ~f:is_bool ts in
  let ints = List.filter ~f:is_int ts in
  let comps = [ Lt; Gt ] @ if no_eq then [] else [ Le; Ge ] in
  let comp =
    match ints with
    | [] -> []
    | _ -> [ mk_bin (mk_choice_exn ints) (BChoice comps) (mk_choice_exn ints) ]
  in
  if k < 3 then (
    match mk_choice (bools @ [ mk_true; mk_false ]) with
    | Ok t -> t
    | Error te ->
        typecheck_err te;
        failwith "bool_choice : type_error" )
  else
    let choice_sq =
      let f c =
        let c' =
          if purefunc then [ mk_un (UChoice [ Not; Id ]) c ]
          else [ mk_true; mk_false; mk_un (UChoice [ Not; Id ]) c ]
        in
        match mk_choice c' with
        | Ok c -> c
        | Error te ->
            typecheck_err te;
            failwith "bool_choice : type_error"
      in
      List.map ~f (bools @ comp @ emptychecks ts)
    in
    mk_app choice_and_or choice_sq

let int_choice ?(nonzero = false) ?(nonone = false) k ts =
  let int_t = List.filter ~f:is_int ts in
  let maybe_zero = if nonzero then [] else [ mk_int 0 ] in
  let maybe_one = if nonone then [] else [ mk_int 1; mk_int (-1) ] in
  let choices = int_t in
  match k with
  | -1 ->
      let choice_sq =
        let f c = mk_un (UChoice [ Neg; Id ]) (mk_choice_exn [ c; mk_int 0 ]) in
        List.map ~f (choices @ [ mk_int 1; mk_int (-1) ])
      in
      mk_app (mk_vt Binop.ac_plus) choice_sq
  | 0 | 1 -> (
      match mk_choice (maybe_zero @ maybe_one @ choices) with
      | Ok c -> c
      | Error te ->
          typecheck_err te;
          failwith "int_choice : type error" )
  | 2 -> (
      match mk_choice (maybe_zero @ [ mk_int 1; mk_int 2 ] @ choices) with
      | Ok c -> c
      | Error te ->
          typecheck_err te;
          failwith "int_choice : type error" )
  | _ ->
      let choice_sq =
        let f c =
          match mk_choice (c :: maybe_zero) with
          | Ok c -> c
          | Error te ->
              typecheck_err te;
              failwith "int_choice : type_error"
        in
        List.map ~f (choices @ [ mk_int 1 ])
      in
      mk_app choice_int_op choice_sq

let div_bin ?(keep_cmp = true) (op : Binop.t) (k : int) : Binop.t =
  match op with
  | Plus | Minus -> if k < 1 then BChoice [ Plus; Minus ] else BChoice [ Max; Min; Minus; Plus ]
  | Max | Min -> if k < 1 then BChoice [ Min; Max ] else BChoice [ Max; Min; Plus; Minus ]
  | Le | Ge | Lt | Gt -> if keep_cmp then op else BChoice [ Le; Lt ]
  | _ -> op

let comp_choice ?(no_eq = false) (k : int) (lhs : term list) (rhs : term list) : term =
  let comps = (if no_eq then [] else [ Le; Ge ]) @ [ Lt; Gt ] in
  let int_operand lt =
    let int_t = List.filter ~f:is_int lt in
    let intc = List.map ~f:(fun t -> mk_choice_exn [ mk_un Neg t; t ]) int_t in
    let x = int_choice ~nonzero:true ~nonone:true 0 lt in
    if k = 1 then
      match mk_binop_of_list_or_fst Plus intc with
      | Some c -> c
      | None -> failwith "error making comparison sketch."
    else x
  in
  let lhs_t = int_operand lhs in
  let rhs_t = int_operand rhs in
  if List.exists ~f:is_bool (lhs @ rhs) then
    let bools = bool_choice 2 (lhs @ rhs) in
    if k > 1 then
      mk_bin
        (mk_un (UChoice [ Id; Not ]) bools)
        (BChoice [ And; Or ])
        (mk_bin lhs_t (BChoice comps) rhs_t)
    else mk_bin bools And (mk_bin lhs_t (BChoice comps) rhs_t)
  else if k > 1 then
    mk_bin
      (mk_choice_exn [ mk_true; mk_bin lhs_t (BChoice comps) rhs_t ])
      (BChoice [ And; Or ])
      (mk_choice_exn [ mk_true; mk_bin lhs_t (BChoice comps) rhs_t ])
  else mk_bin lhs_t (BChoice comps) rhs_t

let pivot_comp_choice ?(no_eq = false) (k : int) (lhs : term list) (rhs : term list) : term =
  (* if k = 0 then  mk_true else *)
  comp_choice ~no_eq k lhs rhs

let div_cmp_choice ?(no_eq = false) (k : int) (lhs : term list) (rhs : term list) : term =
  let int_operand lt = int_choice ~nonzero:true ~nonone:true 0 lt in
  let comps = (if no_eq then [] else [ Le; Ge ]) @ [ Lt; Gt ] in
  let lhs_t = int_operand lhs in
  let rhs_t = int_operand rhs in
  let comp =
    if List.exists ~f:is_bool (lhs @ rhs) then
      let bools = bool_choice 2 (lhs @ rhs) in
      mk_bin bools And (mk_bin lhs_t (BChoice comps) rhs_t)
    else mk_bin lhs_t (BChoice comps) rhs_t
  in
  if k = 0 then comp
  else if k = 1 then mk_bin comp (BChoice [ And; Or ]) comp
  else mk_app choice_and_or [ comp; comp; comp ]

let ok_typed ?(fil = None) (vars : VarSet.t) (th : typ) =
  let fil = Option.(fil >>| fun vs -> VarSet.names vs) in
  let filter_fields fields =
    match fil with
    | Some fil -> List.filter ~f:(fun (fn, _) -> List.mem fil ~equal:String.equal fn) fields
    | None -> fields
  in
  let devl_vars =
    let f v =
      match v.vtype with
      | TStruct (s, fields) ->
          List.map ~f:(fun (fn, _) -> mk_struct_mem ~s fn (mk_vt v)) (filter_fields fields)
      | TList _ -> [ mk_mem (mk_vt v) 0; mk_mem (mk_vt v) 1 ]
      | _ -> [ mk_vt v ]
    in
    List.concat (List.map ~f (Set.to_list vars))
  in
  List.filter
    ~f:(fun x -> match type_of x with Ok typ when ETypes.(typ = th) -> true | _ -> false)
    devl_vars

let rec by_type ?(nonzero = false) ?(cond_hint = Set.empty (module Terms)) ?(fil = None)
    (vars : VarSet.t) (th : typ) (k : int) =
  let gen_conds =
    let f ter =
      let fv = Set.to_list (Lang.Analyze.free_variables ter) in
      match fv with
      | [ x ] -> [ replace_expr ~old:(mk_vt x) ~by:(by_type vars x.vtype 0) ter ]
      | _ -> []
    in
    List.concat (List.map ~f (Set.to_list cond_hint))
  in
  let ok_typed t = List.rev (ok_typed ~fil vars t) in
  match th with
  | TBool ->
      bool_choice k
        (ok_typed TBool @ if k > 0 then gen_conds else [] @ if k > 2 then ok_typed TInt else [])
  | TInt -> int_choice ~nonzero k (ok_typed TInt)
  | _ -> ( match mk_choice (ok_typed th) with Ok x -> x | Error _ -> failwith "Diversify." )

let diversify ?(seeds = None) t k =
  let vars = match seeds with None -> Lang.Analyze.free_variables t | Some x -> x in
  let by_type t = Some (by_type vars t k) in
  let trf f t =
    match t.texpr with
    | EVar (Var v) when Set.mem vars v -> by_type v.vtype
    | EMemStruct (s, field, _) -> (
        match Lang.Structs.field_type s field with Some ft -> by_type ft | None -> None )
    | EBin (op, t1, t2) -> Some (mk_bin (f t1) (div_bin op k) (f t2))
    | EConst c ->
        if k > 0 then
          match c with
          | CInt _ -> Some (int_choice k [ t ])
          | CBool _ -> Some (bool_choice k [ t ])
          | _ -> None
        else None
    | _ -> None
  in
  Transform.transform trf t

let flatten_nested_choices (t : term) =
  let trf _ t =
    match t.texpr with
    | EChoice tl ->
        if List.for_all ~f:is_choice tl then
          let flat_c =
            List.concat_map ~f:(fun t -> match t.texpr with EChoice tl -> tl | _ -> []) tl
          in
          Some (mk_choice_exn (List.dedup_and_sort ~compare:ac_compare flat_c))
        else None
    | _ -> None
  in
  Transform.transform trf t

let or_zero (tl : term list) = mk_choice_exn (tl @ [ mk_int 0 ])

let or_true (tl : term list) = mk_choice_exn (tl @ [ mk_true ])

let differential lvars rvars ?(k = 0) ?(fil = None) ?(resolved = []) (func : l_eqns)
    (inputs : VarSet.t) t =
  let struct_name =
    match func.rstate.vtype with
    | TStruct (s, _) -> s
    | _ -> failwith "unexpected : type not a struct?"
  in

  let resolved =
    let f (v, t) =
      let t' =
        Lang.AcTerm.apply_substs_ac
          (List.map
             ~f:(fun v -> (mk_vt v, mk_struct_mem ~s:struct_name v.vname (mk_vt func.lstate)))
             (Set.elements func.vars))
          t
      in
      (v, t')
    in
    List.map ~f resolved
  in
  let resolved_choice v =
    let vdeps =
      match Map.find func.eqns v.vid with Some eqn -> eqn.edeps | None -> VarSet.empty
    in
    match List.Assoc.find resolved ~equal:Variable.equal v with
    | Some je -> [ je ]
    | None ->
        List.filter_map resolved ~f:(fun (resolved_v, je) ->
            if Set.mem vdeps resolved_v && ETypes.(resolved_v.vtype = v.vtype) then Some je
            else None)
  in
  let allv = lvars $|| rvars in
  let trf f (d, nonzero) t =
    if d > k + 3 then
      match type_of t with Ok atype -> Some (by_type ~nonzero allv atype k) | _ -> Some (mk_int 0)
    else
      match t.texpr with
      | EVar (Var v) when Set.mem inputs v -> Some (by_type ~nonzero rvars v.vtype k)
      | EVar (Var v) -> (
          let base = by_type ~nonzero allv v.vtype k in
          match resolved_choice v with
          | [] -> Some base
          | _ as e ->
              let default = Some (mk_choice_exn (base :: e)) in
              if k = 0 then
                match v.vtype with
                | TInt -> Some (mk_bin base Plus (or_zero e))
                | TBool -> Some (mk_bin base And (or_true e))
                | _ -> default
              else default )
      | EConst (CInt _) -> Some (by_type ~nonzero allv TInt k)
      | EConst (CBool _) -> Some (by_type ~nonzero allv TBool k)
      | EBin (op, t1, t2) ->
          if Binop.is_comp op then
            if List.is_empty (ok_typed ~fil allv TInt) then Some (by_type ~fil allv TBool k)
            else
              let c1 =
                mk_bin
                  (f (d + 1, nonzero) t1)
                  (div_bin ~keep_cmp:(k >= 0) op k)
                  (f (d + 1, nonzero_op op) t2)
              in
              if k > 1 then
                let c2 = by_type allv TBool k in
                Some (mk_app choice_and_or [ c1; c2 ])
              else Some c1
          else if Binop.is_nonlinear op then
            (* Don't go from linear function to non-linear sketch! *)
            match (is_constant t1, is_constant t2) with
            | true, _ -> Some (mk_bin t1 op (f (d + 1, nonzero) t2))
            | _, true -> Some (mk_bin (f (d + 1, nonzero) t1) op t2)
            | _ -> Some (mk_bin (f (d + 1, nonzero) t1) op (f (d + 1, nonzero_op op) t2))
          else Some (mk_bin (f (d + 1, nonzero) t1) op (f (d + 1, nonzero_op op) t2))
      | EIte (c, t1, t2) -> (
          let m_c =
            match mk_choice [ f (d + 1, nonzero) c; by_type allv TBool k ] with
            | Ok c -> mk_ite c (f (d + 1, nonzero) t1) (f (d + 1, nonzero) t2)
            | _ -> f (d + 1, nonzero) t1
          in
          if k <= 1 then Some m_c
          else
            match type_of t1 with
            | Ok TInt -> (
                match mk_choice [ mk_max (f (d + 1, nonzero) t1) (f (d + 1, nonzero) t2); m_c ] with
                | Ok c -> Some c
                | _ -> Some m_c )
            | Ok TBool -> (
                match
                  mk_choice
                    [
                      mk_bin (f (d + 1, nonzero) t1) (BChoice [ And; Or ]) (f (d + 1, nonzero) t2);
                      m_c;
                    ]
                with
                | Ok c -> Some c
                | _ -> Some m_c )
            | _ -> Some m_c )
      | EConst c ->
          if k > 0 then
            match c with
            | CInt _ -> Some (int_choice 0 [ t ])
            | CBool _ -> Some (bool_choice 0 [ t ])
            | _ -> None
          else None
      | _ -> None
  in
  flatten_nested_choices (Transform.term_atransform trf (0, false) t)

let init_term conds (vs : VarSet.t) (t : term) =
  match type_of t with
  | Ok TBool -> (
      match t.texpr with
      | EBin (And, _, _) -> mk_true
      | EBin (Or, _, _) -> mk_false
      | _ -> by_type ~cond_hint:conds vs TBool 0 )
  | Ok TInt -> (
      match t.texpr with
      | EBin (Plus, _, _) -> mk_int 0
      | EBin (Times, _, _) -> mk_int 1
      | _ -> by_type vs TInt 0 )
  | Ok t -> by_type vs t 0
  | _ -> failwith "Cannot create choice of unkown type"

let out_of_predicate_expr ?(max_k = 3) (pred_t : term) (t_out : typ) (args : term list) =
  let arith_op = BChoice [ Min; Max; Plus; Minus ] in
  let boolean_op = BChoice [ And; Or; Xor ] in
  let rec aux_build k t tout =
    match t.texpr with
    | EBin (op, t1, t2) -> (
        match (op, tout) with
        | (Lt | Gt | Le | Ge | Eq | And | Or), TInt ->
            mk_bin
              (aux_build (k + 1) t1 TInt)
              (BChoice [ Min; Max; Plus; Minus ])
              (aux_build (k + 1) t2 TInt)
        | (Plus | Minus | Max | Min), TInt | (Lt | Gt | Le | Ge | Eq), TBool ->
            mk_bin (aux_build (k + 1) t1 TInt) op (aux_build (k + 1) t2 TInt)
        | _ -> failwith "Unsupported predicate binary operator and type combination." )
    | EUn (op, t1) -> (
        match (op, tout) with
        | Not, TInt -> aux_build k t1 TInt
        | Not, TBool -> mk_un op (aux_build (k + 1) t1 TInt)
        | (Abs | Neg), TInt -> mk_un op (aux_build (k + 1) t1 TInt)
        | _ -> failwith "Unsupported predicate and type combination." )
    | EVar _ -> (
        if k >= max_k then
          match tout with
          | TInt -> int_choice 0 args
          | TBool -> bool_choice 0 args
          | _ -> failwith "Unsupported base type."
        else
          match tout with
          | TInt -> mk_bin (int_choice 0 args) arith_op (int_choice 0 args)
          | TBool -> mk_bin (bool_choice 0 args) boolean_op (bool_choice 0 args)
          | _ -> failwith "Unsupported base type." )
    | _ -> failwith "Unexpected predicate expression"
  in
  aux_build 1 pred_t t_out

let make (sinfo : eqs_soln_info) (fn : string) : term =
  let func = sinfo.func_info in
  let k = sinfo.sketching_level in
  let var =
    match VarSet.find_by_name func.vars fn with
    | Some var -> var
    | None -> failwith Fmt.(str "%s is not a known variable." fn)
  in
  let eqn = Map.find_exn func.eqns var.vid in
  let resolved_deps =
    let id_to_j =
      Map.to_alist
        (Map.filter_map
           ~f:(fun data -> match data.ejoin with Either.First j -> Some j | _ -> None)
           sinfo.func_info.eqns)
    in
    List.filter_map
      ~f:(fun (vid, je) ->
        let%map v = VarSet.find_by_id sinfo.func_info.vars vid in
        (v, je))
      id_to_j
  in
  let struct_name =
    match func.rstate.vtype with
    | TStruct (s, _) -> s
    | _ -> failwith "unexpected : type not a struct?"
  in
  let right v = mk_struct_mem ~s:struct_name v.vname (mk_vt func.rstate) in
  let left v = mk_struct_mem ~s:struct_name v.vname (mk_vt func.lstate) in
  let elms ?(vs = func.vars) r typ =
    List.concat
      (List.filter_map (Set.elements vs) ~f:(fun v ->
           if ETypes.(v.vtype = typ) then if r then Some [ right v ] else Some [ right v; left v ]
           else None))
  in
  let of_t typ t =
    let choices =
      List.filter_map ~f:(fun v ->
          if ETypes.(v.vtype = typ) then
            if Set.mem func.vars v then Some (left v)
            else
              match v.vtype with
              | TInt -> Some (mk_choice_exn (elms true TInt))
              | TBool -> Some (mk_choice_exn (elms true TInt))
              | _ -> None
          else None)
    in
    match choices (Set.elements (free_variables t)) with
    | [] -> t
    | [ a ] -> a
    | _ :: _ as l -> mk_choice_exn l
  in
  let lvars t =
    Option.value ~default:(Lang.Analyze.free_variables t)
      (Some (VarSet.singleton sinfo.func_info.lstate))
  in
  let rvars t =
    Option.value ~default:(Lang.Analyze.free_variables t)
      (Some (VarSet.singleton sinfo.func_info.rstate))
  in
  let when_unsolved t =
    let default =
      differential (lvars t) (rvars t)
        ~fil:(Some (eqn.edeps $|| eqn.elifts))
        ~resolved:resolved_deps ~k:sinfo.sketching_level sinfo.func_info
        (sinfo.func_info.collection_inputs $|| VarSet.singleton sinfo.func_info.x)
    in
    let vs = eqn.edeps $|| eqn.elifts in
    let bc_l = by_type (lvars t) TBool 1 in
    let allv_b = by_type (lvars t $|| rvars t) TBool 1 in
    let cond3l = mk_app (mk_vt Binop.ac_or) [ bc_l; bc_l; bc_l ] in
    let cond3 = mk_app (mk_vt Binop.ac_or) [ allv_b; allv_b; bc_l ] in
    match (eqn.erhs.texpr, eqn.einit.texpr) with
    | EBin (And, t1, { texpr = EBin (Or, tv1, tv2); _ }), EConst (CBool b)
    | EBin (And, { texpr = EBin (Or, tv1, tv2); _ }, t1), EConst (CBool b) ->
        if Set.is_empty (Set.inter (free_variables t1) func.vars) then
          match (tv1.texpr, tv2.texpr) with
          | EVar (Var v1), EVar (Var v2) when Variable.(v1 = var || v2 = var) && not b -> (
              let var' = if Variable.(v1 = var) then v2 else v1 in
              match get_init func var'.vid with
              | Some { texpr = EConst (CBool false); _ } ->
                  mk_ite
                    (mk_or (left var) (left var'))
                    (by_type (lvars t $|| rvars t) TBool 1)
                    (right var)
              | Some { texpr = EConst (CBool true); _ } ->
                  mk_ite
                    (mk_and (right var) (mk_not (left var')))
                    (mk_bin
                       (by_type (lvars t) TBool 1)
                       (BChoice [ And; Or ])
                       (by_type (rvars t) TBool 1))
                    (right var)
              | _ -> default t )
          | EVar (Var v1), EVar (Var v2) when Variable.(v1 = var || v2 = var) ->
              mk_ite cond3l cond3 (mk_ite cond3l cond3 cond3)
          | EVar (Var _), EBin (Or, _, _) | EBin (Or, _, _), EVar (Var _) ->
              mk_ite cond3l (right var) (mk_ite cond3l (mk_ite cond3 cond3 cond3) cond3)
          | _, _ -> default t
        else default t
    | EIte ({ texpr = EBin (cop, t1, t2); _ }, _, _), EConst (CInt _) ->
        if k = 0 && Binop.is_comp cop then
          let testeq =
            mk_bin (mk_choice_exn (elms ~vs true TInt)) Eq (mk_choice_exn (elms ~vs true TInt))
          in
          let testok = mk_bin (of_t TInt t1) cop (of_t TInt t2) in
          mk_ite testeq
            (mk_ite testok
               (int_choice (-1) (elms ~vs true TInt @ elms ~vs false TInt))
               (int_choice (-1) (elms ~vs true TInt)))
            (right var)
        else default t
    | _ -> default t
  in
  let when_solved t = subs_state_v sinfo.func_info t in
  match eqn.ejoin with Either.First t -> when_solved t | Either.Second t -> when_unsolved t
