open Base
open Minic
open Lang
open Lang.Alpha
open Lang.Typ
open Lang.Term
open Lang.TermPp
open Utils

exception FunctionalConversionError of Sexp.t

(* Typing utilities for ms_expr *)
let rec ms_typ_of_ms_lhvar (te : ms_typ SM.t) (v : ms_lhvar) : ms_typ option =
  match v with
  | MsVar v -> ( match v.msvtype with Named s -> Map.find te s | t -> Some t )
  | MsMem (v, s) -> (
      Option.(
        ms_typ_of_ms_lhvar te v >>= function
        | Struct tl -> List.find ~f:(fun (x, _) -> String.equal x s) tl >>| snd
        | _ -> None) )
  | MsElt (v, _) -> ( match ms_typ_of_ms_lhvar te v with Some (Seq t) -> Some t | _ -> None )

let conv_table : variable IH.t = Hashtbl.create (module Int)

type mf_stmt = {
  sid : int;
  skind : mf_stmtkind;
  sloc : ms_location;
  mutable schildren : mf_stmt list;
  mutable sparents : mf_stmt list;
}

and mf_stmtkind =
  | FForStmt of mf_iterator * mf_stmt
  | FWhileStmt of term * mf_stmt
  | FIfStmt of term * mf_stmt * mf_stmt
  | FCompStmt of mf_stmt list
  | FDeclStmt of mf_decl
  | FInstrStmt of mf_instr
  | FReturn of term
  | FReturnCstr of term * string
  | FAssertion of mf_assert
  | FEmpty

and mf_assert = FAForall of mf_iterator * term | FATerm of term

and mf_decl = typ * variable * term option

and mf_iterator = FIRange of lhvar * term * term | FIList of lhvar * term | FIEmpty

and mf_instr = term option * term

(* ===================================================================
   Conversion
   ===================================================================== *)

type conv_env = { ftypes : (ms_typ * typ) SM.t; fdefs : (variable * term option) IM.t }

(* CONVERSION FROM MiniSea to intermediary Functional *)
let conv_unop (op : unop) : Unop.t =
  match op with Not -> Not | Neg -> Neg | Abs -> Abs | _ -> failwith "not supported unop"

let conv_const (c : ms_const) : Constant.t =
  match c with MsCInt i -> CInt i | MsCBool b -> CBool b

let rec conv_type ?(name = None) (fenv : conv_env) (t : ms_typ) : typ =
  match t with
  | Int -> TInt
  | Bool -> TBool
  | Attr (t, _) -> conv_type fenv t
  | Seq t -> TList (conv_type fenv t)
  | Function (targs, tres) -> TFun (TTup (List.map ~f:(conv_type fenv) targs), conv_type fenv tres)
  | Struct tl -> (
      let f (x, y) = (x, conv_type fenv y) in
      let l = List.map ~f tl in
      match Structs.type_of_fields l with
      | Some ot -> ot
      | None ->
          (* Anonymous struct *)
          let new_struct_name =
            match name with Some name -> name | None -> get_new_name "$"
            (* Anonymous *)
          in
          Structs.add_name new_struct_name l;
          TStruct (new_struct_name, l) )
  | Named tname -> (
      match Map.find fenv.ftypes tname with
      | Some (_, tval) -> tval
      | None ->
          raise (FunctionalConversionError Sexp.(List [ Atom "type_def_not_found"; Atom tname ])) )

let rec ms_expr_to_term (cenv : conv_env) (e : ms_expr) : term =
  let untyped_t =
    match e with
    | MsEVar msv -> ms_lhvar_to_term cenv msv
    | MsEConst c ->
        let c' = conv_const c in
        mk_term ~ttyp:(Some (type_of_const c')) (EConst (conv_const c))
    | MsEList el -> mk_list (List.map ~f:(ms_expr_to_term cenv) el)
    | MsEStruct mems ->
        let f (n, e) = (n, ms_expr_to_term cenv e) in
        mk_struct (List.map ~f mems)
    | MsBinop (op, e1, e2) ->
        let t1, t2 = (ms_expr_to_term cenv e1, ms_expr_to_term cenv e2) in
        mk_bin t1 op t2
    | MsUnop (uop, t1) ->
        let uop' = conv_unop uop in
        mk_un uop' (ms_expr_to_term cenv t1)
    | MsCond (ct, tt, ft) ->
        mk_ite (ms_expr_to_term cenv ct) (ms_expr_to_term cenv tt) (ms_expr_to_term cenv ft)
    | MsFunCall (f, args) ->
        mk_app (ms_lhvar_to_term cenv (MsVar f)) (List.map ~f:(ms_expr_to_term cenv) args)
  in
  match type_term untyped_t with
  | Ok t -> (
      match t.texpr with
      | EBin (Plus, t1, t2) -> (
          match (t1.ttyp, t2.ttyp) with
          | TList _, TList _ -> { t with texpr = EBin (Concat, t1, t2) }
          | _ -> t )
      | _ -> t )
  | Error (s, t, v) ->
      let pe = Sexp.(List [ Atom "type_error"; Atom s; sexp_of_typ t; sexp_of_expr v ]) in
      Fmt.(pf stdout "%a@;" Sexp.pp_hum pe);
      raise (FunctionalConversionError pe)

and ms_variable_to_var (msv : ms_variable) : variable =
  match Hashtbl.find conv_table msv.msvid with
  | Some v -> v
  | None -> (
      match builtin_varname msv.msvname with
      | Some v -> v
      | None -> raise (UndeclaredVarError msv.msvname) )

and ms_lhvar_to_term (cenv : conv_env) (mlhv : ms_lhvar) : term =
  match mlhv with
  | MsVar msv -> mk_vt (ms_variable_to_var msv)
  | MsElt (mlhv', ie) ->
      let a = ms_lhvar_to_term cenv mlhv' in
      let i = ms_expr_to_term cenv ie in
      mk_bin a At i
  | MsMem (x, n) -> (
      let x' = ms_lhvar_to_term cenv x in
      match resolve_type_of_lhvar cenv x with
      | Struct tl -> (
          let f (x, y) = (x, conv_type cenv y) in
          match Structs.name_of_fields (List.map ~f tl) with
          | Some s -> mk_struct_mem ~s n x'
          | None ->
              Log.error_msg "Undeclared struct";
              raise (FunctionalConversionError Sexp.(Atom "Undeclared struct")) )
      | _ ->
          Log.error_msg (Fmt.str "Field acessor on non-struct variable %a" pp_term x');
          raise (FunctionalConversionError Sexp.(Atom "variable with field acessor not a struct")) )

and resolve_type_of_lhvar (cenv : conv_env) (lhv : ms_lhvar) =
  match lhv with
  | MsVar x -> (
      match x.msvtype with
      | Named n -> (
          match Map.find cenv.ftypes n with
          | Some (t, _) -> t
          | None ->
              raise (FunctionalConversionError Sexp.(List [ Atom "type_def_not_found"; Atom n ])) )
      | _ -> x.msvtype )
  | MsElt (t, _) -> (
      match resolve_type_of_lhvar cenv t with
      | Seq t -> t
      | _ -> raise (FunctionalConversionError Sexp.(List [ Atom "expected seq type" ])) )
  | MsMem (t, mem) -> (
      match resolve_type_of_lhvar cenv t with
      | Struct tl -> (
          match List.Assoc.find tl ~equal:String.equal mem with
          | Some x -> x
          | None -> raise (FunctionalConversionError Sexp.(List [ Atom "wrong struct type" ])) )
      | _ -> raise (FunctionalConversionError Sexp.(List [ Atom "expected struct type" ])) )

let rec conv_initializer (fenv : conv_env) (mst : ms_typ) (init : ms_expr) : expr option =
  match init with
  | MsEVar lhv -> Some (ms_lhvar_to_term fenv lhv).texpr
  | MsEConst c -> Some (EConst (conv_const c))
  | MsEList el -> (
      match mst with
      | Seq mst' ->
          let elts = List.map ~f:(conv_initializer fenv mst') el in
          if List.exists ~f:is_none elts then None
          else Some (EList (List.map ~f:mk_term (List.filter_opt elts)))
      | _ ->
          raise
            (FunctionalConversionError
               Sexp.(Atom "Sequence initializer for a non-sequence variable.")) )
  | MsEStruct ml -> (
      match mst with
      | Struct mlist ->
          let tl =
            List.map
              ~f:(fun (mname, mst') ->
                match List.Assoc.find ml ~equal:String.equal mname with
                | Some ms_e -> Option.(conv_initializer fenv mst' ms_e >>| mk_term)
                | None -> None)
              mlist
          in
          if List.exists ~f:is_none tl then None else Some (ETuple (List.filter_opt tl))
      | _ ->
          raise
            (FunctionalConversionError Sexp.(Atom "Struct initializer for a non-struct variable."))
      )
  | _ ->
      raise (FunctionalConversionError Sexp.(Atom "Got an expresssion that is not an initializer."))

let env_of_globs (stmts : ms_stmt list) (globs : int list) : conv_env =
  let empty_fenv = { ftypes = SM.empty; fdefs = IM.empty } in
  List.fold
    (List.filter stmts ~f:(fun stmt -> List.mem globs stmt.sid ~equal))
    ~init:empty_fenv
    ~f:(fun fenv stmt ->
      match stmt.skind with
      | MsDeclStmt (vmstype, msv, vval_opt) ->
          let vtype = conv_type fenv vmstype in
          let var = mk_var ~name:msv.msvname vtype in
          ( match Hashtbl.add conv_table ~key:msv.msvid ~data:var with
          | `Ok -> ()
          | `Duplicate -> raise (DuplicateVarError msv.msvname) );
          let init_opt = Option.bind ~f:(conv_initializer fenv vmstype) vval_opt in
          {
            fenv with
            fdefs = Map.set ~key:msv.msvid ~data:(var, Option.map ~f:mk_term init_opt) fenv.fdefs;
          }
      | MsTypeDeclStmt (tname, tval) ->
          {
            fenv with
            ftypes =
              Map.set ~key:tname ~data:(tval, conv_type ~name:(Some tname) fenv tval) fenv.ftypes;
          }
      | _ -> fenv)

let ms_iterator_to_f_iterator (cenv : conv_env) (i : ms_iterator) : mf_iterator =
  let simple_var lhv constr =
    match lhv with
    | MsVar v -> constr v
    | _ ->
        raise (FunctionalConversionError Sexp.(Atom "lhvar used in IRange not a simple iterator"))
  in
  match i with
  | MsIRange (lhv, beg, en) ->
      let beg' = ms_expr_to_term cenv beg in
      let en' = ms_expr_to_term cenv en in
      simple_var lhv (fun v -> FIRange (Var (ms_variable_to_var v), beg', en'))
  | MsIList (lhv, e) ->
      simple_var lhv (fun v -> FIList (Var (ms_variable_to_var v), ms_expr_to_term cenv e))
  | MsIEmpty -> FIEmpty

let ms_decl_to_mf_decl (cenv : conv_env) ((t, v, eo) : ms_decl) : mf_decl =
  let ft = conv_type cenv t in
  let fv = ms_variable_to_var v in
  let feo = Option.(eo >>| ms_expr_to_term cenv) in
  (ft, fv, feo)

let ms_instr_to_mf_instr (cenv : conv_env) ((v, e) : ms_instr) : mf_instr =
  let rhs = ms_expr_to_term cenv e in
  match v with Some x -> (Some (ms_lhvar_to_term cenv x), rhs) | None -> (None, rhs)

let ms_assertion_to_assert (cenv : conv_env) (ms_a : ms_assertion) : mf_assert =
  match ms_a with
  | MsAForall (it, e) -> FAForall (ms_iterator_to_f_iterator cenv it, ms_expr_to_term cenv e)
  | MsAExpr e -> FATerm (ms_expr_to_term cenv e)

let rec ms_stmt_to_mf_stmt (cenv : conv_env) (s : ms_stmt) : mf_stmt =
  let sfkind =
    match s.skind with
    | MsForStmt (iter, body) ->
        FForStmt (ms_iterator_to_f_iterator cenv iter, ms_stmt_to_mf_stmt cenv body)
    | MsWhileStmt (cond, body) ->
        FWhileStmt (ms_expr_to_term cenv cond, ms_stmt_to_mf_stmt cenv body)
    | MsIfStmt (cond, st, sf) ->
        FIfStmt (ms_expr_to_term cenv cond, ms_stmt_to_mf_stmt cenv st, ms_stmt_to_mf_stmt cenv sf)
    | MsCompStmt sl -> FCompStmt (List.map ~f:(ms_stmt_to_mf_stmt cenv) sl)
    | MsDeclStmt md -> FDeclStmt (ms_decl_to_mf_decl cenv md)
    | MsTypeDeclStmt (_, _) -> FEmpty
    | MsInstrStmt msi -> FInstrStmt (ms_instr_to_mf_instr cenv msi)
    | MsReturn e -> FReturn (ms_expr_to_term cenv e)
    | MsReturnCstr (e, s) -> FReturnCstr (ms_expr_to_term cenv e, s)
    | MsEmpty -> FEmpty
    | MsAssertion a -> FAssertion (ms_assertion_to_assert cenv a)
  in
  { sid = s.sid; skind = sfkind; sloc = s.sloc; schildren = []; sparents = [] }

let rec fstmt_replace ~(old : term) ~(by : term) (st : mf_stmt) =
  let stk = st.skind in
  match stk with
  | FForStmt (it, body) ->
      let body' = fstmt_replace ~old ~by body in
      { st with skind = FForStmt (it, body') }
  | FWhileStmt (c, t) ->
      let c' = replace_expr ~old ~by c in
      let t' = fstmt_replace ~old ~by t in
      { st with skind = FWhileStmt (c', t') }
  | FIfStmt (c, bt, bf) ->
      let c' = replace_expr ~old ~by c in
      let bt' = fstmt_replace ~old ~by bt in
      let bf' = fstmt_replace ~old ~by bf in
      { st with skind = FIfStmt (c', bt', bf') }
  | FCompStmt stmts -> { st with skind = FCompStmt (List.map ~f:(fstmt_replace ~old ~by) stmts) }
  | FInstrStmt instr ->
      let instr' =
        match instr with
        | Some lv, x -> (Some (replace_expr ~old ~by lv), replace_expr ~old ~by x)
        | None, x -> (None, replace_expr ~old ~by x)
      in
      { st with skind = FInstrStmt instr' }
  | FDeclStmt _ -> st
  | FAssertion _ -> st
  | FReturn r -> { st with skind = FReturn (replace_expr ~old ~by r) }
  | FReturnCstr (t, s) -> { st with skind = FReturnCstr (replace_expr ~old ~by t, s) }
  | FEmpty -> st

and f_iterator_replace ~(old : term) ~(by : term) (it : mf_iterator) =
  match it with
  | FIRange (x, start, finish) ->
      let start' = replace_expr ~old ~by start in
      let finish' = replace_expr ~old ~by finish in
      FIRange (x, start', finish')
  | FIList (x, l) ->
      let l' = replace_expr ~old ~by l in
      FIList (x, l')
  | FIEmpty -> FIEmpty

(* Reaching definitions. *)
(* Map statement_id -> (Map variable id -> (List statement_id, )) *)
type f_defs = (int * term) list IM.t IM.t

let find_reaching_fdefs (stmts : mf_stmt list) : f_defs =
  let join_defs defs1 defs2 =
    Map.fold defs1 ~init:defs2 ~f:(fun ~key:k ~data:defs1_elt defs ->
        match Map.find defs2 k with
        | Some defs2_elt -> Map.set defs ~key:k ~data:(defs1_elt @ defs2_elt)
        | None -> Map.set defs ~key:k ~data:defs1_elt)
  in
  let rec f (rmap, rdefs) stmt =
    let rmap' = Map.set ~key:stmt.sid ~data:rdefs rmap in
    match stmt.skind with
    | FIfStmt (_, s1, s2) ->
        let rmap_t, rdefs_t = f (rmap', rdefs) s1 in
        let rmap_f, rdefs_f = f (rmap', rdefs) s2 in
        (IM.add_all rmap_t rmap_f, join_defs rdefs_t rdefs_f)
    | FCompStmt sl -> List.fold sl ~init:(rmap', rdefs) ~f
    | FInstrStmt i -> (
        match i with
        | Some lh, t ->
            let v = var_of_exn lh in
            let rdefs' = Map.set rdefs ~key:v.vid ~data:[ (stmt.sid, t) ] in
            (rmap', rdefs')
        | None, _ -> (rmap', rdefs) )
    | FForStmt (_, s) ->
        let rmap'', rdefs' = f (rmap, rdefs) s in
        (IM.add_all rmap' rmap'', join_defs rdefs' rdefs)
    | FWhileStmt (_, s) ->
        let rmap'', rdefs' = f (rmap, rdefs) s in
        (IM.add_all rmap' rmap'', join_defs rdefs' rdefs)
    | FDeclStmt (_, v, t) ->
        let rdefs' =
          let declinfo = match t with Some mse -> [ (stmt.sid, mse) ] | None -> [] in
          Map.set ~key:v.vid ~data:declinfo rdefs
        in
        (rmap', rdefs')
    | FAssertion _ | FReturn _ | FReturnCstr _ -> (Map.set ~key:stmt.sid ~data:rdefs rmap, rdefs)
    | FEmpty -> (rmap', rdefs)
  in
  fst (List.fold ~f ~init:(IM.empty, IM.empty) stmts)

let pp_fdefs_at_stmt (frmt : Formatter.t) (defs : f_defs) (sid : int) =
  let defs = Map.find_exn defs sid in
  Map.iteri defs ~f:(fun ~key ~data ->
      if List.length data > 0 then
        Fmt.(pf frmt "%i -> {%a}@." key (list ~sep:comma (pair ~sep:colon int pp_term)) data)
      else ())
