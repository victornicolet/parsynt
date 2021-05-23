open Base
open Term
open TermPp
open Typ

let type_of_exn t =
  match type_of t with
  | Ok t -> t
  | Error e ->
      typecheck_err e;
      failwith "Type checking error"

let count_terms (eq : term -> bool) ~(in_term : term) =
  Transform.recurse
    { init = 0; join = ( + ); case = (fun _ _t -> if eq _t then Some 1 else None) }
    in_term

let is_list_type (t : term) : bool = match type_of t with Ok (TList _) -> true | _ -> false

let main_list_type (t : term) : typ option =
  match type_of t with Ok (TList t) -> Some t | _ -> None

let of_list_term (t : term) : term list option =
  let init = [] in
  let join = ( @ ) in
  let case _ te = if is_list_type te then None else Some [ te ] in
  if is_list_type t then Some (Transform.recurse { init; join; case } t) else None

let occurrences (t : term) (tl : term list) : int =
  let init = 0 in
  let join = ( + ) in
  let case _ t =
    match t.texpr with
    | EConst _ -> Some 0
    | _ -> if List.mem tl t ~equal:Terms.equal then Some 1 else None
  in
  Transform.recurse { init; join; case } t

let apply_substs (substs : (term * term) list) (t : term) : term =
  List.fold ~f:(fun t (old, by) -> replace_expr ~old ~by t) ~init:t substs

(* Short operations *)
let e_not e = EUn (Not, e)

let t_not t = { t with texpr = EUn (Not, t) }

let e_v v = EVar (Var v)

let e_cons l e = EBin (Cons, l, e)

let e_mem v i = EMem (mk_vt v, i)

let e_b b = EConst (CBool b)

let e_i i = EConst (CInt i)

let e_impl a b = EBin (Impl, a, b)

let e_and a b = EBin (And, a, b)

let e_none = EConst CNone

let mk_conj el = match el with hd :: tl -> List.fold_left tl ~init:hd ~f:mk_and | [] -> mk_true

let mk_disj el =
  match el with
  | hd :: tl -> List.fold_left tl ~init:hd ~f:mk_or
  | [] -> failwith "mk_disj only for nonempty lists of expressions."

let rec append_let (t : term) (e : term) : term =
  match t.texpr with
  | ELet (v, b, t') -> { t with texpr = ELet (v, b, append_let t' e) }
  | EEmpty -> e
  | _ -> t

let close_let (t : term) (vars : VarSet.t) : term =
  let struc = mk_struct (List.map ~f:(fun v -> (v.vname, mk_vt v)) (Set.to_list vars)) in
  append_let t struc

let new_struct_var (varset : VarSet.t) : variable * string =
  let mems =
    let f v = (v.vname, v.vtype) in
    List.map ~f (Set.to_list varset)
  in
  Structs.decl_anonymous mems;
  match (Structs.type_of_fields mems, Structs.name_of_fields mems) with
  | Some t, Some tn -> (mk_var t, tn)
  | _, _ -> failwith "Unexpected error: struct should have been automatically declared."

let delete_wrapping_singleton_struct (mname : string) (t : term) =
  let transformer rcall t =
    match t.texpr with
    | EStruct [ (mname', rest) ] when String.equal mname mname' -> Some (rcall rest)
    | _ -> None
  in
  Transform.transform transformer t

(* ============================================================================================= *)
(* =========================   Function Construction Helpers   ================================= *)
(* ============================================================================================= *)

let mk_fold_xz ?(neg = false) mxy mxyz _accum (x1, l1) (x2, l2) (y, _) =
  let m' =
    List.filter mxyz ~f:(fun t ->
        Set.is_empty (Set.diff (Analyze.free_variables t) (VarSet.of_list [ x1; x2 ])))
  in
  let init1, init2, comb1 = if neg then (mk_false, mk_true, Or) else (mk_true, mk_true, And) in
  let xi1, li1, xi2, li2 = if neg then (x2, l2, x1, l1) else (x1, l1, x2, l2) in
  let mzy = replace_expr ~old:(mk_vt y) ~by:(mk_vt x2) mxy in
  (* let m' = List.map ~f:(fun t -> if neg then mk_not t else t) m' in *)
  match mk_binop_of_list_or_fst (if neg then And else Or) m' with
  | Some c ->
      let core = if neg then mzy else mk_and (mk_vt _accum) c in
      mk_foldl ~init:init1 li1
        ~f:
          (mk_lambda [ xi1; _accum ]
             (mk_bin (mk_vt _accum) comb1
                (mk_foldl ~init:init2 li2 ~f:(mk_lambda [ xi2; _accum ] core))))
  | None -> mk_true

let mk_fold_xyz ?(not_z = false) m _accum (x, lx) (y, ly) (z, lz) =
  let m' =
    List.filter m ~f:(fun t ->
        Set.is_empty (Set.diff (Analyze.free_variables t) (VarSet.of_list [ x; y; z ])))
  in
  let m' = List.map ~f:(fun t -> if not_z then t else mk_not t) m' in
  match mk_binop_of_list_or_fst And m' with
  | Some c ->
      let c' = replace_expr ~old:(mk_vt y) ~by:(mk_vt x) c in
      let xyl = mk_concat lx ly in
      mk_foldl ~init:mk_true lz
        ~f:
          (mk_lambda [ z; _accum ]
             (mk_and (mk_vt _accum)
                (mk_foldl ~init:mk_false xyl ~f:(mk_lambda [ x; _accum ] (mk_or (mk_vt _accum) c')))))
  | None -> mk_true

(* ============================================================================================= *)
(* Code simplification passes. *)
(* ============================================================================================= *)

let rec lang_simplify_superfulous_structs (t : term) : term =
  let simplify_singleton_struct (structname : string) (memname : string) (memtyp : typ) (t : term) :
      term option =
    let simplify_singleton_struct_fold f init =
      let new_init, new_accum =
        match init.texpr with
        | EStruct [ (memname', memval) ] when String.equal memname memname' ->
            (Some memval, mk_var ~name:memname' memtyp)
        | _ -> (None, mk_var ~name:"_acc" memtyp)
      in
      let new_f =
        match f.texpr with
        | ELambda ([ elt_var; accum_var ], body) ->
            let new_body =
              delete_wrapping_singleton_struct memname
                (replace_expr
                   ~old:(mk_struct_mem ~s:structname memname (mk_vt accum_var))
                   ~by:(mk_vt new_accum)
                   (lang_simplify_superfulous_structs body))
            in
            Some { f with texpr = ELambda ([ elt_var; new_accum ], new_body) }
        | _ -> None
      in
      match (new_f, new_init) with Some x, Some y -> Some (x, y) | _ -> None
    in
    let simplify_singleton_struct_ite bt bf =
      Some (delete_wrapping_singleton_struct memname bt, delete_wrapping_singleton_struct memname bf)
    in
    match t.texpr with
    | EFoldL (f, init_t, li_t) ->
        Option.(
          simplify_singleton_struct_fold f init_t >>= fun (f', init_t') ->
          Some { t with texpr = EFoldL (f', init_t', li_t) })
    | EFoldR (f, init_t, li_t) ->
        Option.(
          simplify_singleton_struct_fold f init_t >>= fun (f', init_t') ->
          Some { t with texpr = EFoldR (f', init_t', li_t) })
    | EIte (c, bt, bf) ->
        Option.(
          simplify_singleton_struct_ite bt bf >>= fun (bt', bf') ->
          Some { t with texpr = EIte (c, bt', bf') })
    | _ -> None
  in

  let find_and_remove_unwrap_bindings (v : variable) (t : term) : term * variable option =
    let init = None in
    let join t1 t2 =
      match (t1, t2) with
      | Some v1, Some v2 -> if v1.vid = v2.vid then Some v1 else None
      | Some _, None -> t1
      | None, Some _ -> t2
      | _ -> None
    in
    let case rcall t =
      match t.texpr with
      | ELet (Var x, memstruct, body) -> (
          match memstruct.texpr with
          | EMemStruct (_, _, { texpr = EVar (Var v'); _ }) ->
              if v'.vid = v.vid then
                let body', otherv = rcall body in
                Some (body', join (Some x) otherv)
              else None
          | _ -> None )
      | _ -> None
    in
    Transform.transform_and_recurse { init; join; case } t
  in
  let transformer rcall t =
    let te = t.texpr in
    match te with
    | ELet (Var v, t, body) -> (
        match v.vtype with
        | TStruct (structname, [ (memname, memtyp) ]) ->
            if Structs.is_anonymous v.vtype then
              match
                ( find_and_remove_unwrap_bindings v body,
                  simplify_singleton_struct structname memname memtyp t )
              with
              | (body', Some v'), Some t' ->
                  Some { t with texpr = ELet (Var v', rcall t', rcall body') }
              | _ -> None
            else None
        | _ -> None )
    | _ -> None
  in
  Transform.transform transformer t

let remove_superfluous_bindings : term -> term =
  let trf rcall t =
    match t.texpr with
    | ELet (Var v, t', { texpr = EVar (Var v'); _ }) when v.vid = v'.vid -> Some (rcall t')
    | _ -> None
  in
  Transform.transform trf

let reduce_simple_bindings : term -> term =
  let rec is_simple_binding e =
    match e.texpr with
    | EVar _ | EConst _ -> true
    | EMemStruct (_, _, t) -> is_simple_binding t
    | EStruct mems -> List.for_all ~f:is_simple_binding (Utils.ListTools.lsnd mems)
    | EList [] -> true
    | EMem ({ texpr = EVar _; _ }, _) -> true
    | EUn (_, t) -> is_simple_binding t
    | EBin (_, t1, t2) -> is_simple_binding t1 && is_simple_binding t2
    (* | EBin (At, {texpr = EVar _; _}, t') -> is_simple_binding t' *)
    | _ -> false
  in
  let rec f env t =
    match t.texpr with
    | ELet (Var x, e, body) -> (
        let e' = f env e in
        match body.texpr with
        | EVar (Var x') when x.vid = x'.vid -> e'
        | _ ->
            if is_simple_binding e' then
              let new_env = Map.set env ~key:x.vid ~data:e' in
              f new_env body
            else
              let new_env = if Map.mem env x.vid then Map.remove env x.vid else env in
              mk_let (Var x) e' (f new_env body) )
    | EIte (c, bt, bf) -> mk_ite (f env c) (f env bt) (f env bf)
    | EFoldL (func, init, l) ->
        let func' = f env func in
        let init' = Transform.apply_env env init in
        { t with texpr = EFoldL (func', init', Transform.apply_env env l) }
    | ELambda (args, body) ->
        let new_env =
          List.fold ~init:env
            ~f:(fun accum x -> if Map.mem env x.vid then Map.remove accum x.vid else accum)
            args
        in
        { t with texpr = ELambda (args, f new_env body) }
    | _ -> Transform.apply_env env t
  in

  f (Map.empty (module Int))

let lang_opt_passes (t : term) =
  lang_simplify_superfulous_structs t
  |> remove_superfluous_bindings |> reduce_simple_bindings |> Analyze.parallelize_lets
