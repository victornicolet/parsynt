open Base
open Term
open Typ
open TermPp
open Utils
open List
open Result.Let_syntax

let debug = ref false

let verbose = ref false

(* Helper functions *)
let _func : (variable * term) IH.t = Hashtbl.create (module Int)

let use_funcs = ref true

let add_func (f : variable) (body : term) = Hashtbl.add _func ~key:f.vid ~data:(f, body)

let find_func (f : variable) = Hashtbl.find _func f.vid

let find_func_for_reduce (f : variable) = if !use_funcs then find_func f else None

type unfolding = { input : term; from_symb : term; from_init : term }

type unfoldings = unfolding list

let pp_unfolding (f : Formatter.t) x =
  Fmt.(
    braces
      (fun f () ->
        pf f "@[(%a: %a)@;%a :@;%a@;%a :@;%a@;@]"
          (styled (`Fg `Red) string)
          "input" rpp_term x.input
          (styled (`Fg `Red) string)
          "init" rpp_term x.from_init
          (styled (`Fg `Red) string)
          "symb" rpp_term x.from_symb)
      f ())

type env = { evars : VarSet.t; evals : term IM.t }

let pp_env (frmt : Formatter.t) (env : env) =
  let l_env =
    List.map
      ~f:(fun (i, t) -> Option.(VarSet.find_by_id env.evars i >>= fun v -> Some (v, t)))
      (Map.to_alist env.evals)
  in
  Fmt.(list ~sep:comma (option (fun f (v, t) -> pf f "%a <- %a" pp_variable v pp_term t)))
    frmt l_env

let empty_env = { evars = Set.empty (module Variable); evals = Map.empty (module Int) }

exception SymbExeError of string * term

(** --------------------------------------------------------------------------*)

(** Intermediary functions for unfold_once *)

let add_binding (v : variable) (t : term) (env : env) =
  if Set.mem env.evars v then { env with evals = Map.set ~key:v.vid ~data:t env.evals }
  else { evars = v $++ env.evars; evals = Map.set ~key:v.vid ~data:t env.evals }

let add_bindings (bindings : (lhvar * term) list) (env : env) =
  List.fold ~f:(fun env (v, t) -> match v with Var x -> add_binding x t env) ~init:env bindings

let find_binding (v : variable) (env : env) = Map.find env.evals v.vid

let env_extend (env : env) (env' : env) =
  let pickf ~key:_ l =
    match l with `Both (_, l1) -> Some l1 | `Left l1 -> Some l1 | `Right l1 -> Some l1
  in
  { evars = env.evars $|| env'.evars; evals = Map.merge ~f:pickf env.evals env'.evals }

let empty_app_term t f = { t with texpr = EApp (f, []) }

let app_term_cons ft t =
  match t.texpr with
  | EApp (f, args) -> { ft with texpr = EApp (f, args @ [ t ]) }
  | _ -> failhere Caml.__FILE__ "app_term_cons" "First argument has to be app term."

let empty_list_term t = { t with texpr = EList [] }

let list_term_cons lt t =
  match lt.texpr with
  | EList tl -> { lt with texpr = EList (tl @ [ t ]) }
  | _ -> failhere Caml.__FILE__ "list_term_cons" "First argument has to be list term."

let empty_tuple_term t = { t with texpr = ETuple [] }

let tuple_term_cons lt t =
  match lt.texpr with
  | ETuple tl -> { lt with texpr = ETuple (tl @ [ t ]) }
  | _ -> failhere Caml.__FILE__ "tuple_term_cons" "First argument has to be tuple term."

let do_bin t b e1 e2 =
  {
    t with
    texpr =
      ( match b with
      | Cons -> (
          match e1.texpr with
          | EList el -> EList (el @ [ e2 ])
          | EConst CEmpty -> EList [ e2 ]
          | _ -> EBin (Cons, e1, e2) )
      | _ -> EBin (b, e1, e2) );
  }

let do_un t u e =
  match (u, e.texpr) with
  | Not, EConst (CBool true) -> { t with texpr = EConst (CBool false) }
  | Not, EConst (CBool false) -> { t with texpr = EConst (CBool true) }
  | _ -> { t with texpr = EUn (u, e) }

let do_mem t index tup =
  match tup.texpr with
  | ETuple el -> (
      match el @: index with
      | Some eli -> eli
      | None ->
          Log.error (wrap "Out of bounds tuple member acess.");
          raise_s (Sexp.Atom "unfolding error") )
  | _ -> { t with texpr = EMem (tup, index) }

let do_struct_field t sn nm struc =
  match struc.texpr with
  | EStruct mems -> (
      match List.Assoc.find mems ~equal:String.equal nm with
      | Some x -> x
      | None ->
          Log.error (wrap "Invalid struct member acess.");
          raise_s (Sexp.Atom "unfolding error") )
  | EIte (c, { texpr = EStruct t_mems; _ }, { texpr = EStruct f_mems; _ }) -> (
      match
        ( List.Assoc.find t_mems ~equal:String.equal nm,
          List.Assoc.find f_mems ~equal:String.equal nm )
      with
      | Some x1, Some x2 -> mk_ite c x1 x2
      | _ ->
          Log.error (wrap "Invalid struct xmember acess.");
          raise_s (Sexp.Atom "unfolding error") )
  | _ -> { t with texpr = EMemStruct (sn, nm, struc) }

let do_var env v = match find_binding v env with Some e -> e | None -> mk_vt v

let do_lam t vl ebdy = { t with texpr = ELambda (vl, ebdy) }

(* TODO check that do_term doesn't lose any attribute information. *)
let rec do_term (env : env) (t : term) : (term * env, Sexp.t) Result.t =
  match t.texpr with
  | ELet (Var v, e1, e2) ->
      let%bind e1', _ = do_term env e1 in
      do_term (add_binding v e1' env) e2
  | EPLet (bindings, e) -> (
      match
        Result.(
          combine_errors
            (let f (v, t) = do_term env t >>| fun (t', _) -> (v, t') in
             List.map ~f bindings))
      with
      | Ok bindings' -> do_term (add_bindings bindings' env) e
      | Error errs -> Error Sexp.(List errs) )
  | EVar (Var v) -> Ok (do_var env v, env)
  | EHole _ -> Ok (t, env)
  | EEmpty -> Ok (t, env)
  | EMem (tup, index) ->
      let%map tup', _ = do_term env tup in
      (do_mem t index tup', env)
  | EMemStruct (sn, mn, struc) ->
      let%map struc', _ = do_term env struc in
      (do_struct_field t sn mn struc', env)
  | EConst _ -> Ok (t, env)
  | EBin (b, e1, e2) ->
      let%map e1', _ = do_term env e1 and e2', _ = do_term env e2 in
      (do_bin t b e1' e2', env)
  | EUn (u, e1) ->
      let%map e1', _ = do_term env e1 in
      (do_un t u e1', env)
  | ETuple el -> (
      match Result.combine_errors (map ~f:(fun e -> do_term env e) el) with
      | Ok tl -> Ok ({ t with texpr = ETuple (map ~f:fst tl) }, env)
      | Error el -> Error Sexp.(List [ Atom "Tuple"; List el ]) )
  | EList el -> (
      match Result.combine_errors (map ~f:(fun e -> do_term env e) el) with
      | Ok tl -> Ok ({ t with texpr = EList (map ~f:fst tl) }, env)
      | Error el -> Error Sexp.(List [ Atom "List"; List el ]) )
  | EChoice el -> (
      match Result.combine_errors (map ~f:(fun e -> do_term env e) el) with
      | Ok tl -> Ok ({ t with texpr = EChoice (map ~f:fst tl) }, env)
      | Error el -> Error Sexp.(List [ Atom "List"; List el ]) )
  | EStruct el -> (
      let f (s, e) = Result.(do_term env e >>| fun (t, env') -> ((s, t), env')) in
      match Result.combine_errors (map ~f el) with
      | Ok tl -> Ok ({ t with texpr = EStruct (map ~f:fst tl) }, env)
      | Error el -> Error Sexp.(List [ Atom "Struct"; List el ]) )
  | EIte (c, e1, e2) ->
      let%map c', _ = do_term env c and e1', _ = do_term env e1 and e2', _ = do_term env e2 in
      ({ t with texpr = EIte (c', e1', e2') }, env)
  | ESetL (a, i, e) ->
      let%map a', _ = do_term env a and i', _ = do_term env i and e', _ = do_term env e in
      ({ t with texpr = ESetL (a', i', e') }, env)
  | EWith (s, n, b) ->
      let%map s', _ = do_term env s and b', _ = do_term env b in
      ({ t with texpr = EWith (s', n, b') }, env)
  | ELambda (vl, ebdy) ->
      let%map body, _ = do_term env ebdy in
      (do_lam t vl body, env)
  | EApp (f, args) -> (
      match Result.combine_errors (map ~f:(fun e -> do_term env e) args) with
      | Ok l -> (
          let args' = List.map ~f:fst l in
          match f.texpr with
          | ELambda _ ->
              let%map res = apply_lambda env f args' in
              (res, env)
          | EVar (Var fv) -> (
              let%bind f', _ = do_term env f in
              match f'.texpr with
              | ELambda _ ->
                  let%map res = apply_lambda env f' args' in
                  (res, env)
              | _ -> (
                  match find_func fv with
                  | Some (_, fe) ->
                      let%map res = apply_lambda env fe args' in
                      (res, env)
                  | None ->
                      Error
                        Sexp.(
                          List
                            [ Atom "App"; sexp_of_term f'; List (List.map ~f:sexp_of_term args') ])
                  ) )
          | _ -> raise (SymbExeError ("in app, cannot apply", f)) )
      | Error el -> Error Sexp.(List [ Atom "App"; List el ]) )
  | EFoldL (f, ei, le) -> (
      let%bind le', _ = do_term env le and ei', _ = do_term env ei and f', _ = do_term env f in
      match le'.texpr with
      | EList x ->
          let fapp acc elt =
            match acc with
            | Ok (_acc, _env) -> do_term _env (mk_term (EApp (f', [ elt; _acc ])))
            | Error t -> Error t
          in
          fold_left ~f:fapp ~init:(Ok (ei', env)) x
      | EConst CEmpty -> Ok (ei', env)
      | _ ->
          Log.error (printer_msg "Function : %a" pp_term f');
          Log.error (printer_msg "List: %a" pp_term le');
          Log.error (printer_msg "Unfold state: %a" pp_term ei');
          Error Sexp.(List [ Atom "FoldL"; sexp_of_term f'; sexp_of_term ei'; sexp_of_term le' ]) )
  | EFoldR (f, ei, le) -> (
      let%bind le', _ = do_term env le and ei', _ = do_term env ei and f', _ = do_term env f in
      match le'.texpr with
      | EList x ->
          let fapp elt acc =
            match acc with
            | Ok (_acc, _env) -> do_term _env (mk_term (EApp (f', [ elt; _acc ])))
            | Error t -> Error t
          in
          fold_right ~f:fapp ~init:(Ok (ei', env)) x
      | EConst CEmpty -> Ok (ei', env)
      | _ -> Error Sexp.(List [ Atom "FoldR"; sexp_of_term f'; sexp_of_term ei'; sexp_of_term le' ])
      )
  | ELetValues _ -> failwith "Unsupported let-values evluation."

and apply_lambda (env : env) (f : term) (el : term list) : (term, Sexp.t) Result.t =
  match f.texpr with
  | ELambda (vl, body) -> (
      let vars = VarSet.of_list vl in
      match map2 ~f:(fun v e -> (v.vid, e)) vl el with
      | Or_unequal_lengths.Ok l -> (
          match Map.of_alist (module Int) l with
          | `Duplicate_key _ -> raise (SymbExeError ("lambda refers to same variable twice", f))
          | `Ok vals ->
              Result.map ~f:fst (do_term (env_extend env { evars = vars; evals = vals }) body) )
      | Or_unequal_lengths.Unequal_lengths ->
          raise (SymbExeError ("lambda application has wrong number of args", f)) )
  | _ -> raise (SymbExeError ("not a lambda", f))

let reduce ?(env = empty_env) term =
  let%bind t, _ = do_term env term in
  Ok t

let reduce_exn ?(env = empty_env) term =
  match do_term env term with
  | Ok (t, _) -> t
  | Error e ->
      Log.error (printer_msg "In reduce: %a@." Fmt.(box Sexp.pp_hum) e);
      failwith "Error while reducing term."

let unfold ~(f : term) ~(init : term) (l : term list) : (term, Sexp.t) Result.t =
  fold_left
    ~f:(fun rac rin -> Result.bind rac ~f:(fun acc -> apply_lambda empty_env f [ acc; rin ]))
    ~init:(Ok init) l
