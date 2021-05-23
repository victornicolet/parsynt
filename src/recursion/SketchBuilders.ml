open Base
open Lang.AcTerm
open Lang.Analyze
open Lang.ResourceModel
open Lang.SolutionDescriptors
open Lang.Term
open Lang.TermPp
open Lang.Typ
open Lang.Unfold
open Solve.Sketching
open Utils

let include_two_pivots = ref false

let exclude_one_pivot = ref false

let force_two_pivots () =
  exclude_one_pivot := true;
  include_two_pivots := true

let purify_pred (ok_vars : VarSet.t) (t : term) =
  let join ts1 ts2 = Set.union ts1 ts2 in
  let case g _t =
    match _t.texpr with
    | EBin ((And | Or), t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EBin ((And | Or), _, _), EBin ((And | Or), _, _) -> None
        | EBin ((And | Or), _, _), _ ->
            let s2 = Set.is_empty (Set.diff (free_variables t2) ok_vars) in
            if s2 then None
            else
              let t1', others = g t1 in
              Some (t1', Set.add others t2)
        | _, EBin ((And | Or), _, _) ->
            let s1 = Set.is_empty (Set.diff (free_variables t1) ok_vars) in
            if s1 then None
            else
              let t2', others = g t2 in
              Some (t2', Set.add others t1)
        | _ ->
            let s1 = Set.is_empty (Set.diff (free_variables t1) ok_vars) in
            let s2 = Set.is_empty (Set.diff (free_variables t2) ok_vars) in
            if s1 && s2 then None
            else if not s1 then
              let t2', others = g t2 in
              Some (t2', Set.add others t1)
            else
              let t1', others = g t1 in
              Some (t1', Set.add others t2) )
    | _ -> None
  in
  let init = Set.empty (module Terms) in
  let res, t = Transform.transform_and_recurse { case; init; join } t in
  (simplify_easy res, t)

let rec simp_pred (t : term) = match t.texpr with EBin (Or, _, t') -> simp_pred t' | _ -> t

let new_pivot si =
  let x =
    match (fst si.sf_input).vtype with
    | TList t -> mk_var ~name:"pivot" t
    | _ -> mk_var ~name:"pivot" TTop
  in
  (x, project TInt (mk_vt x), mk_var ~name:"f_pivot" (TFun ((fst si.sf_input).vtype, x.vtype)))

let build_partition_divide (budget : cbudget) (si : std_soln) : div_soln list =
  let no_eq = true in
  let div_input_li = mk_var ~name:"X" (fst si.sf_input).vtype in
  let elt_type = match (fst si.sf_input).vtype with TList t -> t | _ -> TTop in
  let pi1, pi_t1, pi_f1 = new_pivot si in
  let pi2, pi_t2, pi_f2 = new_pivot si in
  let x, xt =
    let x = mk_var elt_type in
    (x, project TInt (mk_vt x))
  in
  let partition_bodies (pivcomp_choices, divcomp_choice) =
    let pivot_selec (pivot_v, (pi_f, pi_args), pivcomp_choice) =
      let cond =
        match mk_choice [ mk_false; mk_true; pivcomp_choice ] with
        | Ok c -> c
        | _ -> failwith "Sketch divide: could not make divide bool choice."
      in
      ( pivot_v,
        (pi_f, pi_args),
        mk_foldl
          ~f:(mk_lambda [ x; pivot_v ] (mk_ite cond (mk_vt x) (mk_vt pivot_v)))
          ~init:(mk_un Hd (mk_vt div_input_li))
          (mk_vt div_input_li) )
    in
    let pivots = List.map ~f:pivot_selec pivcomp_choices in
    let mk_one_partition _ =
      let fv = mk_var ~name:"part" (TFun (elt_type, TBool)) in
      (fv, mk_lambda [ x ] divcomp_choice)
    in
    let partitions = List.map ~f:mk_one_partition (List.range 0 (budget.c - 1)) in
    { synt_time = 0.0; solved = false; x = div_input_li; pivots; partitions }
  in
  let one_pivot_instance i j =
    ([ (pi1, (pi_f1, []), pivot_comp_choice i xt pi_t1) ], div_cmp_choice j xt pi_t1)
  in
  let two_pivot_instance i j k =
    ( [
        (pi1, (pi_f1, []), pivot_comp_choice i xt pi_t1);
        (pi2, (pi_f2, [ pi1 ]), pivot_comp_choice j xt (pi_t1 @ pi_t2));
      ],
      div_cmp_choice k xt (pi_t1 @ pi_t2) )
  in
  List.map ~f:partition_bodies
    ( ( if !exclude_one_pivot then []
      else
        [
          one_pivot_instance 0 0;
          one_pivot_instance 1 0;
          one_pivot_instance 0 1;
          one_pivot_instance 1 1;
          ([ (pi1, (pi_f1, []), pivot_comp_choice 0 xt pi_t1) ], div_cmp_choice ~no_eq 2 xt pi_t1);
        ] )
    @
    (* 2 pivots *)
    if !include_two_pivots then
      [
        two_pivot_instance 0 0 0;
        two_pivot_instance 0 1 1;
        two_pivot_instance 0 2 1;
        two_pivot_instance 0 1 2;
      ]
    else [] )

(* ============================================================================================= *)
(*                                   JOIN SKETCHES                                               *)
(* ============================================================================================= *)

let list_constant_time_join (as_set : bool) (s, comp, _t) (args : variable list) : string * term =
  if not as_set then
    let mems = List.map ~f:(fun v -> mk_struct_mem ~s comp (mk_vt v)) args in
    let choice_mems = mk_choice_exn mems in
    let take_or_id t = mk_un (UChoice [ Take (mk_choice_exn []); Id ]) t in
    match mk_binop_of_list_or_fst Concat (List.map ~f:(fun _ -> choice_mems) mems) with
    | Some t -> (comp, take_or_id t)
    | None -> (comp, mk_empty_list)
  else
    let mems = List.map ~f:(fun v -> mk_struct_mem ~s comp (mk_vt v)) args in
    (* Order does not matter. *)
    let sk = List.map ~f:(fun lt -> mk_choice_exn [ mk_list []; lt ]) mems in
    match mk_binop_of_list_or_fst Concat sk with
    | Some t -> (comp, t)
    | None -> (comp, mk_empty_list)

let list_linear_time_join (s, comp, telt) (si : std_soln) (args : variable list) : string * term =
  let s0, sl =
    match args with hd :: tl -> (hd, tl) | _ -> failwith "Join should have at least two args."
  in
  let fold_func =
    let x, accum = (mk_var ~name:"elt" telt, mk_var ~name:"accum" (TList telt)) in
    let t1 = mk_concat (mk_vt accum) (mk_list [ mk_vt x ]) in
    let cx_int = mk_choice (project TInt (mk_vt x)) in
    let cacc_int = mk_choice (List.concat_map ~f:(project TInt) (List.map ~f:mk_vt args)) in
    match (cx_int, cacc_int) with
    | Ok choice_x, Ok choice_acc ->
        let cond = mk_bin choice_x (BChoice [ Lt; Le; Gt; Ge ]) choice_acc in
        mk_lambda [ x; accum ] (mk_ite cond t1 (mk_vt accum))
    | Ok _, _ -> failwith "TODO: linear join sketch accumulator choice failure case"
    | _, _ -> failwith "TODO: linear join sketch choice failure case"
  in
  let fold_list =
    let avl_lists = List.map ~f:(fun v -> mk_struct_mem ~s si.sf_li (mk_vt v)) sl in
    match mk_binop_of_list_or_fst Concat avl_lists with
    | Some t -> t
    | None -> failwith "Join should have at least two args"
  in
  let fold_init = mk_struct_mem ~s si.sf_li (mk_vt s0) in
  (comp, mk_foldl ~f:fold_func ~init:fold_init fold_list)

let list_quadratic_time_join (in_elt : typ) (res_elt : typ) (si : std_soln) (args : variable list) =
  let sname =
    match si.sf_ret with
    | TStruct (s, _) -> s
    | _ -> failwith "Unexpected, should be converted to a struct at this point."
  in
  let get_li_comp t = mk_struct_mem ~s:sname si.sf_li t in
  let s0, s1 =
    match args with
    | [ _ ] | [] -> failwith "Unexpected: not enough arguments for join."
    | [ x; y ] -> (mk_vt x, get_li_comp (mk_vt y))
    | hd :: x :: y :: tl ->
        ( mk_vt hd,
          mk_binop_of_list Concat
            (get_li_comp (mk_vt x))
            (get_li_comp (mk_vt y))
            (List.map ~f:(fun v -> get_li_comp (mk_vt v)) tl) )
  in
  let a' = mk_var ~name:"a" res_elt in
  let a_int_projs = project TInt (mk_vt a') in
  let int_choice = mk_choice_exn a_int_projs in
  let a_bool_projs = project TBool (mk_vt a') in
  let bool_choice = mk_choice_exn (a_bool_projs @ [ mk_true; mk_false ]) in
  let repl_const_by_choice =
    let trf _ t =
      match t.texpr with
      | EConst (CInt _) -> Some int_choice
      | EConst (CBool _) -> Some bool_choice
      | _ -> None
    in
    Transform.transform trf
  in
  let subs at =
    List.map
      ~f:(fun p -> (at, p))
      ( match in_elt with
      | TInt -> a_int_projs
      | TBool -> a_bool_projs
      | _ -> a_int_projs (* Will probably fail. *) )
  in
  let post =
    let at = mk_vt si.sf_post.a in
    mk_lambda [ si.sf_post.s; a' ]
      (repl_const_by_choice (apply_substs_ac (subs at) si.sf_post.body))
  in
  let pre =
    let at = mk_vt si.sf_pre.a in
    mk_lambda [ si.sf_pre.s; a' ] (repl_const_by_choice (apply_substs_ac (subs at) si.sf_pre.body))
  in
  let otimes =
    let at = mk_vt si.sf_otimes.a in
    mk_lambda
      [ si.sf_otimes.e; si.sf_otimes.s ]
      (repl_const_by_choice (apply_substs_ac (subs at) si.sf_otimes.body))
  in
  let oplus =
    let s_inner = si.sf_pre.s in
    let inner_fold =
      mk_foldl
        ~init:(mk_app pre [ mk_vt s_inner; mk_vt a' ])
        ~f:otimes
        (get_li_comp (mk_vt s_inner))
    in
    let lam_body = mk_app post [ inner_fold; mk_vt a' ] in
    mk_lambda [ a'; s_inner ] lam_body
  in
  mk_foldl ~f:oplus ~init:s0 s1

let join_body_of_fields (budget : cbudget) (si : std_soln) (args : variable list)
    (lreqs : (string * term) list) : term =
  let at_preq_component s comp _t pred_t =
    match _t with
    | TList telt ->
        if budget.k = 0 then
          (* Constant time only. *)
          list_constant_time_join si.sf_as_set (s, comp, _t) args
        else if budget.k = 1 then list_linear_time_join (s, comp, telt) si args
        else failwith "Quadratic time join sketched elsewhere."
    | TInt -> (
        let scalars =
          List.concat_map args ~f:(fun v -> project TBool (mk_vt v) @ project TInt (mk_vt v))
        in
        let fst = mk_struct_mem ~s comp (mk_vt (List.hd_exn args)) in
        let lists = List.concat_map args ~f:(fun v -> project_li (mk_vt v)) in
        let c2 = out_of_predicate_expr pred_t TInt scalars in
        match emptychecks ~with_base_c:true lists with
        | [] -> (comp, c2)
        | hd :: _ -> (comp, mk_ite hd fst c2) )
    | _ -> failwith Fmt.(str "%a not supported." pp_typ _t)
  in
  let at_normal_component s comp _t =
    match _t with
    | TList telt ->
        if budget.k = 0 then
          (* Constant time only. *)
          list_constant_time_join si.sf_as_set (s, comp, _t) args
        else if budget.k = 1 then list_linear_time_join (s, comp, telt) si args
        else failwith "Quadratic time join sketched elsewhere."
    | TInt -> (
        let c0 = reduce_exn (mk_struct_mem ~s comp si.sf_post.body) in
        match args with
        | [ s1; s2 ] ->
            let c1 =
              let int_inputs = project TInt (mk_vt si.sf_post.s) in
              apply_substs_ac
                (List.map int_inputs ~f:(fun ax -> (ax, mk_struct_mem ~s comp (mk_vt s1))))
                c0
            in
            let c2 =
              let int_inputs = project TInt (mk_vt si.sf_post.a) in
              apply_substs_ac
                (List.map int_inputs ~f:(fun ax -> (ax, mk_struct_mem ~s comp (mk_vt s2))))
                c1
            in
            (comp, c2)
        | _ ->
            let scalars =
              List.concat_map args ~f:(fun v -> project TBool (mk_vt v) @ project TInt (mk_vt v))
            in
            (comp, int_choice 4 scalars) )
    | TBool ->
        let scalars =
          List.concat_map args ~f:(fun v -> project TBool (mk_vt v) @ project TInt (mk_vt v))
        in
        let lists = List.concat_map args ~f:(fun v -> project_li (mk_vt v)) in
        (comp, bool_choice ~purefunc:true 4 (scalars @ lists))
    | _ -> failwith Fmt.(str "%a not supported." pp_typ _t)
  in
  let at_component s (comp, _t) =
    match List.Assoc.find lreqs ~equal:String.equal comp with
    | Some e -> at_preq_component s comp _t e
    | None -> at_normal_component s comp _t
  in
  match si.sf_ret with
  | TStruct (_s, fields) -> mk_struct (List.map ~f:(at_component _s) fields)
  | _ -> failwith "Unexpected non-struct return type."

let build_join_sketch (ptrue : bool) (b : cbudget) ((_, lreqs) : term option * (string * term) list)
    (si : std_soln) =
  let join_inputs =
    List.map ~f:(fun i -> mk_var ~name:("s" ^ Int.to_string i) si.sf_ret) (List.range 0 b.m)
  in
  let build_nontriv () =
    let join_body = join_body_of_fields b si join_inputs lreqs in
    (join_inputs, join_body)
  in
  let build_triv () =
    let st_li_typ =
      match si.sf_ret with
      | TStruct (_, types) -> List.Assoc.find types ~equal:String.equal si.sf_li
      | TList t -> Some t
      | _ -> None
    in
    let join_body =
      let args =
        let f x =
          match si.sf_ret with
          | TStruct (s, _) -> mk_struct_mem ~s si.sf_li (mk_vt x)
          | TList _ -> mk_vt x
          | _ -> failwith "Unexpected sf_ret in build_join_sketch"
        in
        List.map ~f join_inputs
      in
      match ((fst si.sf_input).vtype, st_li_typ) with
      | TList t1, Some (TList t2) when ETypes.(t1 = t2) -> (
          match mk_binop_of_list_or_fst Concat args with
          | Some f_arg -> mk_app (mk_vt si.sf_func) [ f_arg ]
          | None -> failwith "Cannot make arguments." )
      | TList t1, Some (TList t2) -> list_quadratic_time_join t1 t2 si join_inputs
      | _ -> failwith "Cannot parallelize this."
    in

    (join_inputs, join_body)
  in
  if ptrue && List.is_empty lreqs then build_triv () else build_nontriv ()

(* ============================================================================================ *)
(* ===========================     Lifting Helpers     ======================================== *)
(* ============================================================================================ *)

let mk_ident_val (f : term -> term -> term) (t : typ) : term =
  let base_choice =
    match t with
    | TInt -> mk_choice_exn [ mk_int 1; mk_int 0 ]
    | TBool -> mk_choice_exn [ mk_true; mk_false ]
    | _ -> failwith Fmt.(str "%a is not a valid base type." pp_typ t)
  in
  let x = mk_var t in
  let acc = mk_var t in
  let fe = f (mk_vt x) (mk_vt acc) in
  match fe.texpr with
  | EBin (Max, _, _) -> mk_int (-int_range)
  | EBin (Min, _, _) -> mk_int int_range
  | EBin ((Plus | Minus), _, _) -> mk_int 0
  | EBin ((Times | Div), _, _) -> mk_int 0
  | EIte (c, tt, _) -> (
      match c.texpr with
      | EBin ((Lt | Le), amin, _) ->
          if Set.mem (free_variables amin) x then
            if Set.mem (free_variables tt) x then mk_int int_range
            else if Set.mem (free_variables tt) acc then mk_int (-int_range)
            else mk_int 0
          else if Set.mem (free_variables tt) x then mk_int (-int_range)
          else if Set.mem (free_variables tt) acc then mk_int int_range
          else mk_int 0
      | EBin ((Gt | Ge), amin, _) ->
          if Set.mem (free_variables amin) x then
            if Set.mem (free_variables tt) x then mk_int (-int_range)
            else if Set.mem (free_variables tt) acc then mk_int int_range
            else mk_int 0
          else if Set.mem (free_variables tt) x then mk_int int_range
          else if Set.mem (free_variables tt) acc then mk_int int_range
          else mk_int 0
      | _ -> base_choice )
  | _ -> base_choice

(** Extending an accumulator with a lifting.  *)
let extend_acc ?(use_new = false) (op : acc_op) liftings =
  let nt, ns =
    match op.s.vtype with
    | TStruct (s, fields) ->
        let new_fields = fields @ List.map liftings ~f:(fun (v, _) -> (v.vname, v.vtype)) in
        Lang.Structs.add_name s new_fields;
        (TStruct (s, new_fields), s)
    | _ -> failwith "Unexpected"
  in
  let new_s = mk_var ~name:"_s" nt in
  let new_body =
    match op.body.texpr with
    | EStruct fields ->
        let fields' =
          List.map ~f:(fun (s, t) -> (s, replace_expr ~old:(mk_vt op.s) ~by:(mk_vt new_s) t)) fields
        in
        let fields'' =
          List.map liftings ~f:(fun (v, fun_t) ->
              ( v.vname,
                (if use_new then fun_t (mk_vt op.a) else fun a -> a)
                  (mk_struct_mem ~s:ns v.vname (mk_vt new_s)) ))
        in
        mk_struct (fields' @ fields'')
    | _ -> failwith "Unexpected"
  in
  { op with s = new_s; body = type_term_exn new_body }

let lift_std_soln liftings si =
  let _, new_ret_type =
    match si.sf_ret with
    | TStruct (s, fields) ->
        let new_fields = fields @ List.map liftings ~f:(fun (v, _) -> (v.vname, v.vtype)) in
        Lang.Structs.add_name s new_fields;
        (s, TStruct (s, new_fields))
    | _ -> failwith "Unexpected"
  in
  let new_otimes =
    let otimes_acc = { s = si.sf_otimes.s; a = si.sf_otimes.a; body = si.sf_otimes.body } in
    let new_otimes_acc = extend_acc otimes_acc liftings in
    { si.sf_otimes with s = new_otimes_acc.s; body = new_otimes_acc.body }
  in
  let new_pre = extend_acc si.sf_pre liftings in
  let new_post = extend_acc ~use_new:true si.sf_post liftings in
  let new_init =
    match si.sf_init.texpr with
    | EStruct fields ->
        let new_fields =
          fields @ List.map liftings ~f:(fun (v, f) -> (v.vname, mk_ident_val f v.vtype))
        in
        mk_struct new_fields
    | _ -> failwith "Unexpected"
  in
  let new_funcv =
    match si.sf_func.vtype with
    | TFun (tin, _) ->
        let new_t = TFun (tin, new_ret_type) in
        mk_var ~name:si.sf_func.vname new_t
    | _ -> failwith "Unexpected: function should have function type."
  in
  {
    si with
    sf_init = new_init;
    sf_otimes = new_otimes;
    sf_post = new_post;
    sf_pre = new_pre;
    sf_ret = new_ret_type;
    sf_func = new_funcv;
  }

let lift_comp (reqs : (string * term) list) (si : std_soln) : std_soln =
  let liftings =
    if List.is_empty reqs then
      match (fst si.sf_input).vtype with
      | TList TInt ->
          let v = mk_var ~name:"aux" TInt in
          let f accum x = mk_max accum x in
          [ (v, f) ]
      | TList (TStruct (inp_s, mems)) ->
          let f (m, t) =
            match t with
            | TInt ->
                let v = mk_var ~name:"aux" TInt in
                let v' = mk_var ~name:"aux" TInt in
                let f1 x accum = mk_max accum (mk_struct_mem ~s:inp_s m x) in
                let f2 x accum = mk_min accum (mk_struct_mem ~s:inp_s m x) in
                Some [ (v, f1); (v', f2) ]
            | _ -> None
          in
          List.concat (List.filter_map mems ~f)
      | _ -> []
    else
      match (fst si.sf_input).vtype with
      | TList TInt ->
          let v1 = mk_var ~name:"aux" TInt in
          let f1 accum x = mk_max accum x in
          let v2 = mk_var ~name:"aux" TInt in
          let f2 accum x = mk_min accum x in
          [ (v1, f1); (v2, f2) ]
      | TList (TStruct (inp_s, mems)) ->
          let f (m, t) =
            match t with
            | TInt ->
                let v = mk_var ~name:"aux" TInt in
                let f x accum = mk_max accum (mk_struct_mem ~s:inp_s m x) in
                Some (v, f)
            | _ -> None
          in
          List.filter_map mems ~f
      | _ -> []
  in
  lift_std_soln liftings si
