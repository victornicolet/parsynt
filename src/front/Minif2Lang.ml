open Base
open Minic2MiniF
open Lang
open Lang.Typ
open Lang.Term
open Lang.TermPp
open Lang.TermUtils

let conversion_error s = raise (FunctionalConversionError s)

(* Small helper functions *)
let empty_exprs = Set.empty (module Expressions)

let esingle s = Set.singleton (module Expressions) s

let wrap (s : mf_stmt) sk = { s with skind = sk }

(* Worker function for capture_iteration *)
let rec capt_stmt ~idx (s : mf_stmt) : Set.M(Expressions).t * mf_stmt =
  match s.skind with
  | FForStmt (i, b) ->
      let v1, i' = capt_iterator ~idx i in
      let v2, b' = capt_stmt ~idx b in
      (Set.union v1 v2, wrap s (FForStmt (i', b')))
  | FWhileStmt (_, _) -> conversion_error Sexp.(Atom "Unsupported while stmt.")
  | FIfStmt (c, s1, s2) ->
      let v1, c' = capt_term ~idx c in
      let v2, s1' = capt_stmt ~idx s1 in
      let v3, s2' = capt_stmt ~idx s2 in
      (Set.union_list (module Expressions) [ v1; v2; v3 ], wrap s (FIfStmt (c', s1', s2')))
  | FCompStmt sl ->
      let v1, sl' =
        List.fold ~init:(empty_exprs, []) sl ~f:(fun (vs', sl') s' ->
            let v, s'' = capt_stmt ~idx s' in
            (Set.union vs' v, sl' @ [ s'' ]))
      in
      (v1, wrap s (FCompStmt sl'))
  | FInstrStmt ins ->
      let v', ins' = capt_instr ~idx ins in
      (v', wrap s (FInstrStmt ins'))
  (* Ignore these statements. *)
  | FAssertion _ | FDeclStmt _ | FReturn _ | FReturnCstr (_, _) | FEmpty ->
      (empty_exprs, wrap s FEmpty)

and capt_iterator ~(idx : term) (it : mf_iterator) : Set.M(Expressions).t * mf_iterator =
  match it with
  | FIRange (x, beg, en) ->
      let v1, beg' = capt_term ~idx beg in
      let v2, en' = capt_term ~idx en in
      (Set.union v1 v2, FIRange (x, beg', en'))
  | FIList (x, l) ->
      let v1, l' = capt_term ~idx l in
      (v1, FIList (x, l'))
  | FIEmpty -> (empty_exprs, FIEmpty)

and capt_term ~(idx : term) (t : term) : Set.M(Expressions).t * term =
  let f _ t =
    match t.texpr with
    | EVar (Var v) when Terms.equal t idx -> Some (mk_vt v, esingle (EVar (Var v)))
    | EBin (At, a, v) -> if Terms.equal v idx then Some (mk_bin a At v, esingle a.texpr) else None
    | _ -> None
  in
  let t', v' =
    Transform.transform_and_recurse
      { init = Set.empty (module Expressions); join = Set.union; case = f }
      t
  in
  (v', t')

and capt_instr ~(idx : term) (i : mf_instr) =
  match i with
  | Some v, t -> (
      match v.texpr with
      | EVar _ ->
          let v', t' = capt_term ~idx t in
          (v', (Some v, t'))
      | _ ->
          let v1, tv' = capt_term ~idx v in
          let v2, t' = capt_term ~idx t in
          (Set.union v1 v2, (Some tv', t')) )
  | None, _ -> conversion_error Sexp.(Atom "Unsupported function call with side effects.")

let capture_iteration (body : mf_stmt) (iterator : mf_iterator) : variable * term * mf_stmt =
  let v_idx, idx, t_idx, maybe_a =
    match iterator with
    | FIRange (Var v, _, _) -> (v, mk_vt v, v.vtype, None)
    | FIList (Var v, a) -> (v, mk_vt v, v.vtype, Some a)
    | FIEmpty -> conversion_error Sexp.(Atom "Empty range")
  in
  let is_of_type_idx e = match type_of_expr e with Ok t -> ETypes.equal t t_idx | _ -> false in
  let indexed_exprs, body' = capt_stmt ~idx body in
  let f e = is_list_type (mk_term e) in
  if Set.for_all ~f indexed_exprs then
    let l = Set.to_list indexed_exprs in
    let f (collections, newbody) ai =
      Fmt.(pf stdout "Term: %a[%a].@." pp_term (mk_term ai) pp_term idx);
      let tarray =
        match main_list_type (mk_term ai) with Some t -> t | None -> failwith "Unexpected case."
      in
      let p = mk_var ~name:"_a" tarray in
      let newbody = fstmt_replace ~old:(mk_term ai) ~by:(mk_vt p) newbody in
      ((p, mk_term ai) :: collections, newbody)
    in
    let collections, newbody = List.fold ~init:([], body') ~f l in
    match collections with
    | [] -> (
        match maybe_a with
        | Some a -> (v_idx, a, newbody)
        | _ -> Utils.failhere Caml.__FILE__ "capture_iteration" "Unsupported collection traversal."
        )
    | [ (p, a) ] -> (p, a, newbody) (* //TODO more info about hte list indexed *)
    | _ -> Utils.failhere Caml.__FILE__ "capture_iteration" "Unsupported collection traversal."
  else if Set.for_all ~f:is_of_type_idx indexed_exprs && Set.length indexed_exprs = 1 then
    match iterator with
    | FIRange (Var x, lo, hi) -> (x, mk_app (mk_vt Lang.Term._RANGE_) [ lo; hi ], body')
    | FIList (Var x, li) -> (x, li, body')
    | FIEmpty -> failwith "Unexpected empty iterator."
  else failwith "Unsupported"

(* ============================================================================================= *)
(* MF --> LANG *)
(* ============================================================================================= *)
let mk_state_struct (varset : VarSet.t) : term =
  let f v = (v.vname, mk_vt v) in
  let l = Set.to_list varset in
  Structs.decl_anonymous (List.map ~f:(fun v -> (v.vname, v.vtype)) l);
  mk_struct (List.map ~f l)

let rec term_as_lhvar (t : term) : lhvar * (term -> term) =
  match t.texpr with
  | EVar v -> (v, fun t -> t)
  | EBin (At, a, i) ->
      let a', f = term_as_lhvar a in
      (a', fun t -> f (mk_set_l a i t))
  | EMemStruct (_, fieldname, memt) ->
      let x, f = term_as_lhvar memt in
      (x, fun t -> f (mk_with memt fieldname t))
  | _ -> raise (FunctionalConversionError (Sexp.Atom "term_as_lhvar only for at or fieldstruct"))

(*
  Convert a mf_stmt to a term.
 *)
let unwrap_vars_from_state_struct structname statev accumvars init_t =
  let f accum v = mk_let (Var v) (mk_struct_mem ~s:structname v.vname (mk_vt statev)) accum in
  List.fold ~f ~init:init_t (Set.to_list accumvars)

let rec convert_statement (stmt : mf_stmt) : VarSet.t * term =
  let stmt_kind = stmt.skind in
  let rcall = convert_statement in
  match stmt_kind with
  | FForStmt (iter, body) ->
      let fold_func_elt, fold_list, fold_body = capture_iteration body iter in
      let accumvars, fold_func_body = convert_statement fold_body in
      let accumvars = accumvars $&& Lang.Analyze.free_variables fold_func_body in
      let statev, structname = new_struct_var accumvars in
      let fold_term =
        let fold_func =
          mk_lambda [ fold_func_elt; statev ]
            (unwrap_vars_from_state_struct structname statev accumvars
               (close_let fold_func_body accumvars))
        in
        let fold_init = mk_state_struct accumvars in
        mk_term (EFoldL (fold_func, fold_init, fold_list))
      in
      let wrapped_fold =
        mk_let (Var statev) fold_term
          (unwrap_vars_from_state_struct structname statev accumvars mk_empty_term)
      in
      (accumvars, wrapped_fold)
  | FWhileStmt (_, _) -> failwith "//TODO While not supported"
  | FIfStmt (cond, stmt_t, stmt_f) ->
      let vt, tt = convert_statement stmt_t in
      let vf, tf = convert_statement stmt_f in
      let mod_vars = vt $|| vf in
      let statev, structname = new_struct_var mod_vars in
      let t =
        mk_let (Var statev)
          (mk_ite cond (close_let tt mod_vars) (close_let tf mod_vars))
          (unwrap_vars_from_state_struct structname statev mod_vars mk_empty_term)
      in
      (mod_vars, t)
  | FCompStmt stmts ->
      let f (vars, accum) stmt =
        let x, xt = rcall stmt in
        (vars $|| x, append_let accum xt)
      in
      List.fold_left ~f ~init:(VarSet.empty, mk_empty_term) stmts
  | FDeclStmt (_, x, ot) -> (
      match ot with
      | Some t -> (VarSet.singleton x, mk_let (Var x) t mk_empty_term)
      | _ -> (VarSet.empty, mk_empty_term) )
  | FInstrStmt instr -> convert_instr instr
  | FReturn t -> (VarSet.empty, t)
  | FReturnCstr (t, _) -> (VarSet.empty, t)
  | FEmpty -> (VarSet.empty, mk_empty_term)
  | FAssertion _ -> failwith "Leftover assertion?"

and convert_instr (mfi : mf_instr) : VarSet.t * term =
  match mfi with
  | Some x, t -> (
      let y, f = term_as_lhvar x in
      match y with Var v -> (VarSet.singleton v, mk_let (Var v) (f t) mk_empty_term) )
  | None, t ->
      Utils.Log.error (fun f () -> Fmt.(pf f "Instruction with side effects: %a;" pp_term t));
      failwith "Unsupported side effects."

let minif2lang (stmt : mf_stmt) : term =
  let statev, t = convert_statement stmt in
  let free_vars = Lang.Analyze.free_variables t in
  let statev = free_vars $&& statev in
  ignore (Lang.TermUtils.new_struct_var statev);
  lang_opt_passes t

(*  (Lang.TermUtils.close_let t statev) *)
