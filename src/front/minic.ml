open Base
open Lang.Typ
open Lexing
open Utils

exception TypeError of string

type ms_position = position

type ms_location = { lstart : ms_position; lend : ms_position }

let zero_pos = { pos_fname = "INIT"; pos_lnum = 0; pos_cnum = 0; pos_bol = 0 }

let zero_loc = { lstart = zero_pos; lend = zero_pos }

type a_identifier = string

type ms_typ =
  | Int
  | Bool
  | Attr of ms_typ * a_expr
  | Seq of ms_typ
  | Function of ms_typ list * ms_typ
  | Struct of (string * ms_typ) list
  | Named of string

and a_stmt = { skind : a_stmtkind; sloc : ms_location }

and a_stmtkind =
  | AForStmt of a_iterator * a_stmt
  | AWhileStmt of a_expr * a_stmt
  | AIfStmt of a_expr * a_stmt * a_stmt
  | ACompStmt of a_stmt list
  | ADeclStmt of a_decl
  | ATypeDeclStmt of a_identifier * ms_typ
  | AInstrStmt of a_instr
  | AReturn of a_expr
  | AReturnCstr of a_expr * string
  | AAssertion of assertion_expr
  | AEmpty

and assertion_expr = AAForall of a_iterator * a_expr | AAExpr of a_expr

and a_iterator =
  | AIRange of a_identifier * a_expr * a_expr
  | AIList of a_identifier * a_expr
  | AIEmpty

and a_instr = a_lhvar option * a_expr

and a_lhvar = AVar of a_identifier | AElt of a_lhvar * a_expr | AMem of a_lhvar * string

and a_const = ACInt of int | ACBool of bool

and a_decl = ms_typ * a_identifier * a_expr option

and a_expr =
  | AEVar of a_lhvar
  | AEConst of a_const
  | AEList of a_expr list
  | AEStruct of (string * a_expr) list
  | ABinop of binop * a_expr * a_expr
  | AUnop of unop * a_expr
  | ACond of a_expr * a_expr * a_expr
  | AFunCall of a_identifier * a_expr list

type a_fundecl = ms_typ * a_identifier * a_arg list * a_stmt

and a_arg = ms_typ * a_identifier

type a_program = AFunctions of a_fundecl list | ABody of a_stmt list

let mkAStmt loc stmtkind = { sloc = loc; skind = stmtkind }

let mkAStmt_defloc stmtkind = { sloc = zero_loc; skind = stmtkind }

exception UndeclaredVarError of string

exception UndeclaredFuncError of string

exception UnexpectedArguments of string

exception UndeclaredTypeError of string

exception DuplicateVarError of string

type ms_variable = { msvname : string; msvid : int; msvtype : ms_typ }

let sexp_of_ms_variable v = Sexp.(List [ Atom v.msvname; Atom (Int.to_string v.msvid) ])

module MsVariable = struct
  module T = struct
    type t = ms_variable

    let compare x y = compare x.msvid y.msvid

    let equal x y = x.msvid = y.msvid

    let ( = ) x y = equal x y

    let sexp_of_t = sexp_of_ms_variable

    let hash = Hashtbl.hash
  end

  include T
  include Comparator.Make (T)
end

module MsVarSet = struct
  module MsVs = Set.M (MsVariable)
  include MsVs

  type elt = MsVariable.t

  let singleton = Set.singleton (module MsVariable)

  let empty = Set.empty (module MsVariable)

  let of_list = Set.of_list (module MsVariable)

  let elements = Set.elements

  let map f vs : t = of_list (List.map ~f (elements vs))

  let filter = Set.filter

  let find_by_id vs id : elt option = Set.max_elt (filter ~f:(fun elt -> elt.msvid = id) vs)

  let find_by_name vs name : elt option =
    Set.max_elt (filter ~f:(fun elt -> String.equal elt.msvname name) vs)

  let vids_of_vs vs : int list = List.map ~f:(fun vi -> vi.msvid) (elements vs)

  let has_vid vs id : bool = List.mem (vids_of_vs vs) id ~equal

  let bindings vs = List.map ~f:(fun elt -> (elt.msvid, elt)) (elements vs)

  let names vs = List.map ~f:(fun elt -> elt.msvname) (elements vs)

  let types vs = List.map ~f:(fun elt -> elt.msvtype) (elements vs)

  let record vs = List.map ~f:(fun elt -> (elt.msvname, elt.msvtype)) (elements vs)

  let add_prefix vs prefix =
    of_list (List.map ~f:(fun v -> { v with msvname = prefix ^ v.msvname }) (elements vs))

  let iset vs ilist =
    of_list (List.filter ~f:(fun vi -> List.mem ilist vi.msvid ~equal) (elements vs))
end

(* Statements, expressions, iterators, ... *)
type ms_stmt = {
  sid : int;
  skind : ms_stmtkind;
  sloc : ms_location;
  mutable schildren : ms_stmt list;
  mutable sparents : ms_stmt list;
}

and ms_stmtkind =
  | MsForStmt of ms_iterator * ms_stmt
  | MsWhileStmt of ms_expr * ms_stmt
  | MsIfStmt of ms_expr * ms_stmt * ms_stmt
  | MsCompStmt of ms_stmt list
  | MsDeclStmt of ms_decl
  | MsTypeDeclStmt of string * ms_typ
  | MsInstrStmt of ms_instr
  | MsReturn of ms_expr
  | MsReturnCstr of ms_expr * string
  | MsAssertion of ms_assertion
  | MsEmpty

and ms_assertion = MsAForall of ms_iterator * ms_expr | MsAExpr of ms_expr

and ms_iterator =
  | MsIRange of ms_lhvar * ms_expr * ms_expr
  | MsIList of ms_lhvar * ms_expr
  | MsIEmpty

and ms_instr = ms_lhvar option * ms_expr

and ms_lhvar = MsVar of ms_variable | MsElt of ms_lhvar * ms_expr | MsMem of ms_lhvar * string

and ms_const = MsCInt of int | MsCBool of bool

and ms_decl = ms_typ * ms_variable * ms_expr option

and ms_expr =
  | MsEVar of ms_lhvar
  | MsEConst of ms_const
  | MsEList of ms_expr list
  | MsEStruct of (string * ms_expr) list
  | MsBinop of binop * ms_expr * ms_expr
  | MsUnop of unop * ms_expr
  | MsCond of ms_expr * ms_expr * ms_expr
  | MsFunCall of ms_variable * ms_expr list

type ms_fundecl = ms_typ * ms_variable * ms_arg list * ms_stmt

and ms_arg = ms_typ * ms_variable

type ms_program = MsFunctions of ms_fundecl list | MsBody of ms_stmt list

(* Builtins *)
let builtin_vars =
  Utils.SM.from_bindings
    [
      ("INT_MAX", { msvname = "INT_MAX"; msvid = Lang.Term._INT_MAX.vid; msvtype = Int });
      ("INT_MIN", { msvname = "INT_MIN"; msvid = Lang.Term._INT_MIN.vid; msvtype = Int });
      ( "range",
        { msvname = "range"; msvid = Lang.Term._RANGE_.vid; msvtype = Function ([ Int; Int ], Int) }
      );
    ]

let builtin_funcs =
  Utils.SM.from_bindings
    [
      ( "max",
        fun args ->
          match args with
          | [] -> (
              match SM.find "INT_MAX" builtin_vars with
              | Some v -> MsEVar (MsVar v)
              | None -> raise (UndeclaredVarError "INT_MAX") )
          | [ a ] -> a
          | [ a; b ] -> MsBinop (Max, a, b)
          | _ -> raise (UnexpectedArguments "Too many arguments for max.") );
      ( "min",
        fun args ->
          match args with
          | [] -> (
              match SM.find "INT_MIN" builtin_vars with
              | Some v -> MsEVar (MsVar v)
              | None -> raise (UndeclaredVarError "INT_MIN") )
          | [ a ] -> a
          | [ a; b ] -> MsBinop (Min, a, b)
          | _ -> raise (UnexpectedArguments "Too many arguments for min.") );
      ( "abs",
        fun args ->
          match args with
          | [ a ] -> MsCond (MsBinop (Gt, a, MsEConst (MsCInt 0)), a, MsUnop (Neg, a))
          | _ -> raise (UnexpectedArguments "Too many arguments for abs.") );
    ]

let is_builtin_func f = Map.mem builtin_funcs f

let is_builtin_var (vname : string) : bool = Map.mem builtin_vars vname

let make_builtin bname bargs : ms_expr =
  match Map.find builtin_funcs bname with
  | Some builtin -> builtin bargs
  | None -> raise (UndeclaredFuncError (bname ^ " is not a builtin func."))

let builtin_var vname : ms_variable =
  match Map.find builtin_vars vname with
  | Some var -> var
  | None -> raise (UndeclaredVarError (vname ^ " is not a builtin var."))

(*  Utils *)
let rec var_of_lh (lh : ms_lhvar) : ms_variable =
  match lh with MsVar v -> v | MsElt (a, _) -> var_of_lh a | MsMem (s, _) -> var_of_lh s

(* Convert AlphaSea -> BetaSea *)
let __VARS__ : ms_variable IH.t = Hashtbl.create (module Int)

let _idc_ = ref 100

let mkStmt loc s =
  let stmt = { skind = s; sloc = loc; sid = !_idc_; schildren = []; sparents = [] } in
  Int.incr _idc_;
  stmt

type env = ms_variable SM.t

type tenv = ms_typ SM.t

let empty_tenv : tenv = Map.empty (module String)

let rec get_fresh_name seed : string =
  try
    Hashtbl.iter __VARS__ ~f:(fun v ->
        if String.equal v.msvname seed then
          raise (Not_found_s Sexp.(List [ Atom "Not_found"; Atom v.msvname ]))
        else ());
    seed
  with Not_found_s _ ->
    Int.incr _idc_;
    get_fresh_name (seed ^ Int.to_string !_idc_)

let add_var (name : string) (typ : ms_typ) : ms_variable =
  let var = { msvname = name; msvtype = typ; msvid = !_idc_ } in
  ignore (Hashtbl.add __VARS__ ~key:!_idc_ ~data:var);
  Int.incr _idc_;
  var

let get_var (vid : int) : ms_variable option = Hashtbl.find __VARS__ vid

let rec convert_1 (prg : a_program) : ms_program =
  let conv_args argslist =
    List.fold argslist
      ~f:(fun (l, m) (t, n) ->
        let v = add_var n t in
        let m' = Map.add m ~key:n ~data:v in
        match m' with
        | `Duplicate -> (l @ [ (t, v) ], raise (DuplicateVarError n))
        | `Ok m'' -> (l @ [ (t, v) ], m''))
      ~init:([], Map.empty (module String))
  in
  let conv_fdecl funcs (t, vn, args, body) =
    let argst = List.map ~f:(fun (t, _) -> t) args in
    let v = add_var vn (Function (argst, t)) in
    let nargs, env = conv_args args in
    let nbody, _, _ = convert_stmt env empty_tenv body in
    funcs @ [ (t, v, nargs, nbody) ]
  in
  match prg with
  | AFunctions flist -> MsFunctions (List.fold flist ~init:[] ~f:conv_fdecl)
  | ABody stmts ->
      let stmts', _, _ =
        List.fold stmts
          ~init:([], Map.empty (module String), empty_tenv)
          ~f:(fun (stmt_l, env, tenv) stmt ->
            let stmt', env', tenv' = convert_stmt env tenv stmt in
            (stmt_l @ [ stmt' ], env', tenv'))
      in
      MsBody stmts'

and convert_type (t_env : tenv) (mst : ms_typ) : ms_typ =
  match (mst : ms_typ) with
  | Int -> Int
  | Bool -> Bool
  | Attr (t, _) -> convert_type t_env t
  | Seq t -> Seq (convert_type t_env t)
  | Function (targs, tres) -> Function (List.map ~f:(convert_type t_env) targs, tres)
  | Struct s -> Struct (List.map ~f:(fun (n, t) -> (n, convert_type t_env t)) s)
  | Named nm -> (
      match Map.find t_env nm with Some t -> t | None -> raise (UndeclaredTypeError nm) )

and convert_stmt (env : env) (tenv : tenv) (astmt : a_stmt) : ms_stmt * env * tenv =
  let mkStmt = mkStmt astmt.sloc in
  match astmt.skind with
  | AEmpty -> (mkStmt MsEmpty, env, tenv)
  | ADeclStmt (at, avname, maybe_init) ->
      let var = add_var avname at in
      let env' = Map.set ~key:var.msvname ~data:var env in
      let init' = Option.map ~f:(convert_expr env) maybe_init in
      (mkStmt (MsDeclStmt (convert_type tenv at, var, init')), env', tenv)
  | ATypeDeclStmt (tname, tval) ->
      let tenv' = Map.set ~key:tname ~data:tval tenv in
      (mkStmt (MsTypeDeclStmt (tname, convert_type tenv tval)), env, tenv')
  | AInstrStmt ainstr -> (mkStmt (MsInstrStmt (convert_instr env ainstr)), env, tenv)
  | AForStmt (ait, abdy) -> (
      let msit, env', extra_decl = convert_iterator env ait in
      let bdy, _, _ = convert_stmt env' tenv abdy in
      let for_stmt = mkStmt (MsForStmt (msit, bdy)) in
      match extra_decl with
      | Some decl ->
          let decl_stmt = mkStmt (MsDeclStmt decl) in
          (mkStmt (MsCompStmt [ decl_stmt; for_stmt ]), env, tenv)
      | None -> (for_stmt, env, tenv) )
  | AWhileStmt (c, abdy) ->
      let bdy, _, _ = convert_stmt env tenv abdy in
      (mkStmt (MsWhileStmt (convert_expr env c, bdy)), env, tenv)
  | AIfStmt (c, s1, s2) ->
      let s1', _, _ = convert_stmt env tenv s1 in
      let s2', _, _ = convert_stmt env tenv s2 in
      (mkStmt (MsIfStmt (convert_expr env c, s1', s2')), env, tenv)
  | ACompStmt stmtl ->
      let stmts, _, _ =
        List.fold stmtl ~init:([], env, tenv) ~f:(fun (l, e, t) stmt ->
            let s', e', t' = convert_stmt e t stmt in
            (l @ [ s' ], e', t'))
      in
      (mkStmt (MsCompStmt stmts), env, tenv)
  | AReturn ae -> (mkStmt (MsReturn (convert_expr env ae)), env, tenv)
  | AReturnCstr (ae, prop) -> (mkStmt (MsReturnCstr (convert_expr env ae, prop)), env, tenv)
  | AAssertion a -> (
      let aexpr, extra_decl = convert_assertion env a in
      let assert_stmt = mkStmt (MsAssertion aexpr) in
      match extra_decl with
      | Some decl ->
          let decl_stmt = mkStmt (MsDeclStmt decl) in
          (mkStmt (MsCompStmt [ decl_stmt; assert_stmt ]), env, tenv)
      | None -> (assert_stmt, env, tenv) )

and convert_assertion (env : env) (a : assertion_expr) : ms_assertion * ms_decl option =
  match a with
  | AAForall (it, e) ->
      let ms_it, new_env, add_decl = convert_iterator env it in
      (MsAForall (ms_it, convert_expr new_env e), add_decl)
  | AAExpr e -> (MsAExpr (convert_expr env e), None)

and convert_iterator (env : env) (ait : a_iterator) : ms_iterator * env * ms_decl option =
  match ait with
  | AIRange (i, i0, iN) ->
      (MsIRange (convert_lhvar env (AVar i), convert_expr env i0, convert_expr env iN), env, None)
  | AIList (e, le) -> (
      let le' = convert_expr env le in
      match (Map.find env e, le') with
      | None, MsEVar (MsVar listvar) -> (
          match listvar.msvtype with
          | Seq t ->
              let var = add_var e t in
              let env' = Map.set ~key:var.msvname ~data:var env in
              (MsIList (MsVar var, le'), env', Some (t, var, None))
          | _ -> raise (UndeclaredVarError e) )
      | _ -> (MsIList (convert_lhvar env (AVar e), convert_expr env le), env, None) )
  | AIEmpty -> (MsIEmpty, env, None)

and convert_instr (env : env) (ainstr : a_instr) : ms_instr =
  let maybe_vname, aexpr = ainstr in
  (Option.map ~f:(convert_lhvar env) maybe_vname, convert_expr env aexpr)

and convert_expr (env : env) (ae : a_expr) : ms_expr =
  match ae with
  | AEVar v -> MsEVar (convert_lhvar env v)
  | AEConst c -> MsEConst (convert_const c)
  | AEList l -> MsEList (List.map ~f:(convert_expr env) l)
  | AEStruct m -> MsEStruct (List.map ~f:(fun (s, e) -> (s, convert_expr env e)) m)
  | ABinop (op, e1, e2) -> MsBinop (op, convert_expr env e1, convert_expr env e2)
  | AUnop (op, e1) -> MsUnop (op, convert_expr env e1)
  | ACond (c, e1, e2) -> MsCond (convert_expr env c, convert_expr env e1, convert_expr env e2)
  | AFunCall (f, args) -> (
      match Map.find env f with
      | Some vf -> MsFunCall (vf, List.map ~f:(convert_expr env) args)
      | None ->
          if is_builtin_func f then make_builtin f (List.map ~f:(convert_expr env) args)
          else raise (UndeclaredFuncError f) )

and convert_lhvar (env : env) (av : a_lhvar) : ms_lhvar =
  match av with
  | AVar vname -> (
      match Map.find env vname with
      | Some vi -> MsVar vi
      | None ->
          if is_builtin_var vname then MsVar (builtin_var vname)
          else raise (UndeclaredVarError vname) )
  | AElt (v, e) -> MsElt (convert_lhvar env v, convert_expr env e)
  | AMem (v, m) -> MsMem (convert_lhvar env v, m)

and convert_const (ac : a_const) : ms_const =
  match ac with ACInt i -> MsCInt i | ACBool b -> MsCBool b

let link_stmts (p : ms_program) : ms_program =
  let rec f stmt =
    let add_child c = stmt.schildren <- stmt.schildren @ [ c ] in
    match stmt.skind with
    | MsForStmt (_, s) ->
        add_child s;
        f s
    | MsWhileStmt (_, s) ->
        add_child s;
        f s
    | MsIfStmt (_, st, sf) ->
        add_child st;
        add_child sf;
        [ st; sf ]
    | MsCompStmt sl -> (
        match sl with
        | [] -> [ stmt ]
        | hd :: tl ->
            add_child hd;
            List.fold tl ~init:[ hd ] ~f:(fun prev_s_l s ->
                List.iter ~f:(fun prev_s -> prev_s.schildren <- prev_s.schildren @ [ s ]) prev_s_l;
                f s) )
    | MsEmpty | MsDeclStmt _ | MsTypeDeclStmt _ | MsInstrStmt _ | MsReturnCstr _ | MsReturn _
    | MsAssertion _ ->
        [ stmt ]
  in
  match p with
  | MsFunctions funcs ->
      MsFunctions
        (List.map
           ~f:(fun (t, x, args, b) ->
             let _ = f b in
             (t, x, args, b))
           funcs)
  | MsBody sl -> (
      let sl = mkStmt zero_loc (MsCompStmt sl) in
      let _ = f sl in
      match sl.skind with
      | MsCompStmt sl -> MsBody sl
      | _ -> failwith "Unexpected failure in link_stmts." )

let convert (p : a_program) : ms_program =
  let p' = convert_1 p in
  link_stmts p'

(* **************************************** *)

let index_of_iterator (it : ms_iterator) : MsVarSet.t =
  match it with
  | MsIRange (v, _, _) -> MsVarSet.singleton (var_of_lh v)
  | MsIList (v, _) -> MsVarSet.singleton (var_of_lh v)
  | MsIEmpty -> MsVarSet.empty

(* Visitors *)

let write_set_of stmt =
  let rec f w s =
    match s.skind with
    | MsReturn _ | MsReturnCstr _ | MsTypeDeclStmt _ | MsDeclStmt _ -> w
    | MsInstrStmt (ox, _) -> ( match ox with Some x -> Set.add w (var_of_lh x) | None -> w )
    | MsForStmt (_, s) | MsWhileStmt (_, s) -> f w s
    | MsIfStmt (_, s1, s2) -> f (f w s1) s2
    | MsCompStmt sl -> List.fold sl ~init:w ~f
    | MsEmpty -> w
    | MsAssertion _ -> w
  in
  f MsVarSet.empty stmt

let vars_of (e : ms_expr) =
  let rec f r e =
    match e with
    | MsEVar v -> Set.add r (var_of_lh v)
    | MsEConst _ -> r
    | MsEList l -> List.fold ~f ~init:r l
    | MsEStruct m -> List.fold ~f:(fun r (_, e) -> f r e) ~init:r m
    | MsBinop (_, e1, e2) -> f (f r e1) e2
    | MsUnop (_, e1) -> f r e1
    | MsCond (c, et, ef) -> f (f (f r c) et) ef
    | MsFunCall (_, el) -> List.fold el ~init:r ~f
  in
  f MsVarSet.empty e

(* TODO *)

let read_set_of stmt =
  let rec f r s =
    match s.skind with
    | MsReturn e | MsReturnCstr (e, _) -> Set.union r (vars_of e)
    | MsDeclStmt (_, _, eo) -> ( match eo with Some e -> Set.union r (vars_of e) | None -> r )
    | MsInstrStmt (_, e) -> Set.union (vars_of e) r
    | MsForStmt (it, s) ->
        let of_it =
          match it with
          | MsIRange (_, _from, _to) -> Set.union (vars_of _from) (vars_of _to)
          | MsIList (_, l) -> vars_of l
          | MsIEmpty -> MsVarSet.empty
        in
        f (Set.union r of_it) s
    | MsWhileStmt (c, s) -> f (Set.union r (vars_of c)) s
    | MsIfStmt (c, s1, s2) -> f (f (Set.union r (vars_of c)) s1) s2
    | MsCompStmt sl -> List.fold sl ~init:r ~f
    | MsAssertion _ | MsTypeDeclStmt _ | MsEmpty -> r
  in

  f MsVarSet.empty stmt

let sids_in (stmt : ms_stmt) : IS.t =
  let rec f is s =
    let is = Set.add is s.sid in
    match s.skind with
    | MsAssertion _ | MsInstrStmt _ | MsDeclStmt _ | MsTypeDeclStmt _ | MsEmpty | MsReturnCstr _
    | MsReturn _ ->
        is
    | MsForStmt (_, s) | MsWhileStmt (_, s) -> f is s
    | MsIfStmt (_, s1, s2) -> f (f is s1) s2
    | MsCompStmt sl -> List.fold sl ~init:is ~f
  in

  f IS.empty stmt

let rec find_stmt (stmt : ms_stmt) (sid : int) : ms_stmt option =
  if stmt.sid = sid then Some stmt
  else
    match stmt.skind with
    | MsAssertion _ | MsInstrStmt _ | MsDeclStmt _ | MsTypeDeclStmt _ | MsEmpty | MsReturnCstr _
    | MsReturn _ ->
        None
    | MsForStmt (_, s) | MsWhileStmt (_, s) -> find_stmt s sid
    | MsIfStmt (_, s1, _) -> (
        match find_stmt s1 sid with Some x -> Some x | None -> find_stmt s1 sid )
    | MsCompStmt sl -> (
        let l = List.filter ~f:is_some (List.map ~f:(fun s -> find_stmt s sid) sl) in
        match l with [] -> None | hd :: _ -> hd )

let find_stmt_in_prog (p : ms_program) (sid : int) : ms_stmt =
  let of_stmtlist sl =
    let l = List.filter ~f:is_some (List.map ~f:(fun s -> find_stmt s sid) sl) in
    match l with [] -> None | hd :: _ -> hd
  in
  let maybe_stmt =
    match p with
    | MsFunctions fl -> of_stmtlist (List.map ~f:(fun (_, _, _, s) -> s) fl)
    | MsBody sl -> of_stmtlist sl
  in

  match maybe_stmt with
  | Some x -> x
  | None -> raise_s Sexp.(List [ Atom "Not_found stmt_in_prog"; Int.sexp_of_t sid ])

(**
   Reaching defs:
   Map from statement ids to map ms_variable id -> list of statement id
*)

type program_rdefs = ms_expr list IM.t IM.t

let reaching_defs (stmts : ms_stmt list) : program_rdefs =
  let join_defs defs1 defs2 =
    Map.fold defs1 ~init:defs2 ~f:(fun ~key:k ~data:defs1_elt defs ->
        match Map.find defs2 k with
        | Some defs2_elt -> Map.set defs ~key:k ~data:(defs1_elt @ defs2_elt)
        | None -> Map.set defs ~key:k ~data:defs1_elt)
  in
  let rec f (rmap, rdefs) stmt =
    let rmap' = Map.set ~key:stmt.sid ~data:rdefs rmap in
    match stmt.skind with
    | MsIfStmt (_, s1, s2) ->
        let rmap_t, rdefs_t = f (rmap', rdefs) s1 in
        let rmap_f, rdefs_f = f (rmap', rdefs) s2 in
        (IM.add_all rmap_t rmap_f, join_defs rdefs_t rdefs_f)
    | MsCompStmt sl -> List.fold sl ~init:(rmap', rdefs) ~f
    | MsInstrStmt i -> (
        let rmap' = Map.set ~key:stmt.sid ~data:rdefs rmap in
        match i with
        | Some lh, t ->
            let v = var_of_lh lh in
            let rdefs' = Map.set rdefs ~key:v.msvid ~data:[ t ] in
            (rmap', rdefs')
        | None, _ -> (rmap', rdefs) )
    | MsForStmt (_, s) ->
        let rmap' = Map.set ~key:stmt.sid ~data:rdefs rmap in
        let rmap'', rdefs' = f (rmap, rdefs) s in
        (IM.add_all rmap' rmap'', join_defs rdefs' rdefs)
    | MsWhileStmt (_, s) ->
        let rmap' = Map.set ~key:stmt.sid ~data:rdefs rmap in
        let rmap'', rdefs' = f (rmap, rdefs) s in
        (IM.add_all rmap' rmap'', join_defs rdefs' rdefs)
    | MsDeclStmt (_, v, t) ->
        let rmap' = Map.set ~key:stmt.sid ~data:rdefs rmap in
        let rdefs' =
          let declinfo = match t with Some mse -> [ mse ] | None -> [] in
          Map.set ~key:v.msvid ~data:declinfo rdefs
        in
        (rmap', rdefs')
    | MsAssertion _ | MsReturn _ | MsReturnCstr _ -> (Map.set ~key:stmt.sid ~data:rdefs rmap, rdefs)
    | MsTypeDeclStmt _ | MsEmpty -> (rmap', rdefs)
  in
  fst (List.fold ~f ~init:(IM.empty, IM.empty) stmts)

type ms_variables = {
  state_vars : MsVarSet.t;
  index_vars : MsVarSet.t;
  used_vars : MsVarSet.t;
  all_vars : MsVarSet.t;
}

let loop_variables it stmt =
  let x = write_set_of stmt in
  let y = read_set_of stmt in
  let i = index_of_iterator it in
  { state_vars = x; used_vars = y; index_vars = i; all_vars = Set.union (Set.union x y) i }

(* ============================================================================================
   Pretty printing utilities
   ============================================================================================  *)

let print_with_id = ref false

let string_of_unop unop = match unop with Neg -> "-" | Not -> "!" | Abs -> "abs" | _ -> "CHOICE"

let string_of_binop binop =
  match binop with
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Div -> "/"
  | Max -> "max"
  | Min -> "min"
  | And -> "&&"
  | Or -> "||"
  | Lt -> "<"
  | Gt -> ">"
  | Ge -> ">="
  | Le -> "<="
  | Eq -> "=="
  | Mod -> "%"
  | _ -> "CHOICE"

let rec pp_ms_typ (frmt : Formatter.t) (mt : ms_typ) =
  match mt with
  | Int -> Fmt.(pf frmt "int")
  | Bool -> Fmt.(pf frmt "boolean")
  | Attr (t, _) -> Fmt.(pf frmt "(%a @ _)" pp_ms_typ t)
  | Seq t -> Fmt.(pf frmt "%a*" pp_ms_typ t)
  | Function (t1, t2) -> Fmt.(pf frmt "(%a -> %a)" (list pp_ms_typ) t1 pp_ms_typ t2)
  | Struct fields -> Fmt.(pf frmt "{%a}" (list ~sep:semi (pair ~sep:sp string pp_ms_typ)) fields)
  | Named s -> Fmt.(pf frmt "%s" s)

let str_of_ms_typ (t : ms_typ) : string = Fmt.to_to_string pp_ms_typ t

let rec pp_stmt (form : Formatter.t) s =
  (if !print_with_id then Fmt.(pf form "%i|" s.sid));
  match s.skind with
  | MsForStmt (it, s) -> Fmt.(pf form "@[<v 2>for (%a)@;%a@;@]" pp_iterator it pp_stmt s)
  | MsWhileStmt (e, s) -> Fmt.(pf form "@[<v 2>while (%a)@;%a@;@]" (pp_expr ~par:false) e pp_stmt s)
  | MsIfStmt (c, s1, s2) -> (
      match s2.skind with
      | MsEmpty -> Fmt.(pf form "@[<hv 2>@,if (%a)@;%a@,@]" (pp_expr ~par:false) c pp_stmt s1)
      | _ ->
          Fmt.(
            pf form "@[<hv 2>@,if (%a)@;%a@;else@;%a@,@]" (pp_expr ~par:false) c pp_stmt s1 pp_stmt
              s2) )
  | MsCompStmt stmt_list ->
      Fmt.(pf form "@[<hv 2>{@;%a@;<1 -2>}@]" (list ~sep:sp pp_stmt) stmt_list)
  | MsDeclStmt decl -> pp_decl form decl
  | MsTypeDeclStmt (tname, tval) -> Fmt.(pf form "@[<h 2>typedecl %s %a;@]@." tname pp_ms_typ tval)
  | MsInstrStmt instr -> pp_instr form instr
  | MsReturn e -> Fmt.(pf form "@[<h 2>return@ %a;@]" (pp_expr ~par:false) e)
  | MsReturnCstr (e, prop) -> Fmt.(pf form "@[<h 2>return@ %a as %s;@]" (pp_expr ~par:false) e prop)
  | MsAssertion a -> Fmt.(pf form "@[<h 2>assert %a;@]" pp_assertion a)
  | MsEmpty -> ()

and pp_assertion form a =
  match a with
  | MsAForall (i, e) ->
      Fmt.(pf form "@[<hov 2>forall(%a){%a}@]" pp_iterator i (pp_expr ~par:false) e)
  | MsAExpr e -> pp_expr form e

and pp_const form c =
  match c with MsCInt i -> Fmt.(pf form "%i" i) | MsCBool b -> Fmt.(pf form "%b" b)

and pp_lhvar form lhv =
  match lhv with
  | MsVar v ->
      if !print_with_id then Fmt.(pf form "(%s : %i)" v.msvname v.msvid)
      else Fmt.(pf form "%s" v.msvname)
  | MsElt (v, e) -> Fmt.(pf form "%a[%a]" pp_lhvar v (pp_expr ~par:false) e)
  | MsMem (s, m) -> Fmt.(pf form "%a.%s" pp_lhvar s m)

and pp_expr ?(par = false) form e =
  let lpar, rpar = ((if par then "(" else ""), if par then ")" else "") in
  match e with
  | MsEVar v -> pp_lhvar form v
  | MsEConst c -> pp_const form c
  | MsEList l -> Fmt.(pf form "[%a]" (box (list ~sep:comma (pp_expr ~par:false))) l)
  | MsEStruct m ->
      Fmt.(
        pf form "@[<v 2>{%a}@]"
          (list ~sep:semi (pair ~sep:(fun form () -> pf form "=") string pp_expr))
          m)
  | MsBinop (op, e1, e2) -> (
      match op with
      | Max | Min ->
          Fmt.(
            pf form "@[<hov 2>%s(%a,@;%a)@]" (string_of_binop op) (pp_expr ~par:false) e1
              (pp_expr ~par:false) e2)
      | _ ->
          Fmt.(
            pf form "@[<hov 2>%s%a@;%s@;%a%s@]" lpar (pp_expr ~par:true) e1 (string_of_binop op)
              (pp_expr ~par:true) e2 rpar) )
  | MsUnop (op, e) -> (
      match op with
      | Abs -> Fmt.(pf form "@[<hov 2>%s(%a)@]" (string_of_unop op) (pp_expr ~par:false) e)
      | _ ->
          Fmt.(pf form "@[<hov 2>%s%s@;%a%s@]" lpar (string_of_unop op) (pp_expr ~par:true) e rpar)
      )
  | MsCond (c, e1, e2) ->
      Fmt.(
        pf form "@[<hov 2>%s%a?@;%a : @;%a%s@]" lpar (pp_expr ~par:false) c (pp_expr ~par:false) e1
          (pp_expr ~par:false) e2 rpar)
  | MsFunCall (f, args) ->
      Fmt.(pf form "@[<hov 2>%s(%a)@]" f.msvname (list ~sep:comma pp_expr) args)

and pp_instr form instr =
  match instr with
  | Some lh, e -> Fmt.(pf form "%a = %a;" pp_lhvar lh (pp_expr ~par:false) e)
  | None, e -> pp_expr form e

and pp_decl form decl =
  match decl with
  | t, v, Some e -> Fmt.(pf form "%a %s = %a;" pp_ms_typ t v.msvname (pp_expr ~par:false) e)
  | t, v, None -> Fmt.(pf form "%a %s;" pp_ms_typ t v.msvname)

and pp_iterator form it =
  match it with
  | MsIRange (i, i0, iN) ->
      Fmt.(pf form "%a = %a .. %a" pp_lhvar i (pp_expr ~par:false) i0 (pp_expr ~par:false) iN)
  | MsIList (i, l) -> Fmt.(pf form "%a in %a" pp_lhvar i (pp_expr ~par:false) l)
  | MsIEmpty -> Fmt.(pf form "</! empty range>")

let pp_arg form (t, v) = Fmt.(pf form "%a %s" pp_ms_typ t v.msvname)

let pp_fundecl form (t, fn, args, body) =
  Fmt.(
    pf form "@[<v 4>%a %s(%a){@;%a@;}@]" pp_ms_typ t fn.msvname (list ~sep:sp pp_arg) args pp_stmt
      body)

let pp_program form pg =
  match pg with
  | MsFunctions fs -> List.iter ~f:Fmt.(pf form "%a@." pp_fundecl) fs
  | MsBody stmts ->
      Fmt.(pf form "program@.");
      List.iter ~f:Fmt.(pf form "%a@." pp_stmt) stmts
