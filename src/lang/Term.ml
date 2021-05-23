open Typ
open Utils
open Base
module O = Option

let sexp_of_variable v = Sexp.(List [ Atom "var"; Atom v.vname ])

(*  Atom (Int.to_string v.vid); sexp_of_typ v.vtype]) *)

let variable_of_sexp s =
  match s with
  | Sexp.(List [ Atom "var"; Atom vname; Atom id; typ ]) ->
      { vname; vid = Int.of_string id; vtype = typ_of_sexp typ; vattrs = [] }
  | _ -> raise (Sexp.Of_sexp_error (failwith "Not a variable sexp.", s))

let pp_variable f v = Fmt.((styled (`Fg `Cyan) string) f v.vname)

let pp_id_var f v = Fmt.(pf f "(%i : %s)" v.vid v.vname)

let dump_variable f v = Fmt.(string f v.vname)

module Variable = struct
  module T = struct
    type t = variable

    let compare x y = compare x.vid y.vid

    let equal x y = x.vid = y.vid

    let ( = ) x y = equal x y

    let sexp_of_t = sexp_of_variable

    let hash = Hashtbl.hash
  end

  include T
  include Comparator.Make (T)

  let is_anonymous (v : t) : bool = List.mem v.vattrs Anonymous ~equal:Poly.equal

  let make_anonymous (v : t) : t =
    if is_anonymous v then v else { v with vattrs = Anonymous :: v.vattrs }

  let is_builtin (v : t) : bool = List.mem v.vattrs Builtin ~equal:Poly.equal

  let make_builtin (v : t) : t =
    if is_anonymous v then v else { v with vattrs = Builtin :: v.vattrs }

  let has_attr (attr : vattribute) (v : t) = List.mem ~equal:Poly.equal v.vattrs attr

  let id (v : t) = v.vid

  let name (v : t) = v.vname
end

module VarSet = struct
  module V = Set.M (Variable)
  include V

  type elt = variable

  let empty = Set.empty (module Variable)

  let singleton = Set.singleton (module Variable)

  let elements vs = Set.elements vs

  let of_list = Set.of_list (module Variable)

  let map f vs : t = of_list (List.map ~f (elements vs))

  let max_elt = Set.max_elt

  let min_elt = Set.max_elt

  let find_by_id vs id : elt option = max_elt (Set.filter ~f:(fun elt -> elt.vid = id) vs)

  let has_name vs name : bool = Set.exists ~f:(fun elt -> String.equal elt.vname name) vs

  let find_by_name vs name : elt option =
    max_elt (Set.filter ~f:(fun elt -> String.equal elt.vname name) vs)

  let vids_of_vs vs : int list = List.map ~f:(fun vi -> vi.vid) (elements vs)

  let has_vid vs id : bool = List.mem ~equal:( = ) (vids_of_vs vs) id

  let bindings vs = List.map ~f:(fun elt -> (elt.vid, elt)) (elements vs)

  let names vs = List.map ~f:(fun elt -> elt.vname) (elements vs)

  let types vs = List.map ~f:(fun elt -> elt.vtype) (elements vs)

  let record vs = List.map ~f:(fun elt -> (elt.vname, elt.vtype)) (elements vs)

  let substitute (subs : (elt * elt) list) (vs : t) =
    let f nu v =
      match List.Assoc.find subs ~equal:Variable.equal v with
      | Some v' -> v' :: nu
      | None -> v :: nu
    in
    of_list (List.fold ~f ~init:[] (Set.elements vs))

  let to_struct vs =
    let r = record vs in
    (Structs.decl_of_vars r, r)

  let add_prefix vs prefix =
    of_list (List.map ~f:(fun v -> { v with vname = prefix ^ v.vname }) (elements vs))

  let iset vs ilist =
    of_list (List.filter ~f:(fun vi -> List.mem ilist vi.vid ~equal:( = )) (elements vs))

  let pp_var_names formatter vs = Fmt.(list ~sep:comma pp_variable formatter (elements vs))

  let pp formatter vs = Fmt.(list ~sep:sp pp_id_var formatter (elements vs))

  let dump formatter vs = Fmt.Dump.(list pp_id_var formatter (elements vs))

  let of_sh sh = SH.fold (fun _ v vset -> Set.add vset v) sh (Set.empty (module Variable))
end

let ( $-> ) : (variable -> variable) -> VarSet.t -> VarSet.t = VarSet.map

let ( $-- ) v elt : VarSet.t = Set.remove elt v

let ( $.- ) : VarSet.t -> VarSet.t -> VarSet.t = Set.diff

let ( $++ ) v elt : VarSet.t = Set.add elt v

let ( $&& ) : VarSet.t -> VarSet.t -> VarSet.t = Set.inter

let ( $|| ) : VarSet.t -> VarSet.t -> VarSet.t = Set.union

module Binop = struct
  module T = struct
    type t = binop [@@deriving sexp]

    let get_id (op : t) : int =
      match op with
      | Times -> 0
      | Div -> 1
      | Plus -> 2
      | Minus -> 3
      | Max -> 4
      | Min -> 5
      | And -> 6
      | Or -> 7
      | Xor -> 8
      | Impl -> 9
      | Cons -> 10
      | Concat -> 11
      | Lt -> 12
      | Gt -> 13
      | Le -> 14
      | Ge -> 15
      | Eq -> 16
      | Mod -> 17
      | At -> 18
      | BChoice _ -> 19

    let compare b1 b2 = compare (get_id b1) (get_id b2)

    let rec is_nonlinear = function
      | Times | Div | Mod -> true
      | BChoice l -> List.exists l ~f:is_nonlinear
      | _ -> false

    let ac_ops = [ Plus; Times; And; Or; Max; Min; Xor ]

    let a_ops = [ Concat ]

    let ac_plus =
      { vname = "+"; vid = get_id Plus; vtype = TFun (TMany TInt, TInt); vattrs = [ Builtin ] }

    let ac_times =
      { vname = "*"; vid = get_id Times; vtype = TFun (TMany TInt, TInt); vattrs = [ Builtin ] }

    let ac_max =
      { vname = "max"; vid = get_id Max; vtype = TFun (TMany TInt, TInt); vattrs = [ Builtin ] }

    let ac_min =
      { vname = "min"; vid = get_id Min; vtype = TFun (TMany TInt, TInt); vattrs = [ Builtin ] }

    let ac_and =
      { vname = "&&"; vid = get_id And; vtype = TFun (TMany TBool, TBool); vattrs = [ Builtin ] }

    let ac_or =
      { vname = "||"; vid = get_id Or; vtype = TFun (TMany TBool, TBool); vattrs = [ Builtin ] }

    let ac_opvars =
      [
        (Plus, ac_plus);
        (Times, ac_times);
        (Max, ac_max);
        (Min, ac_min);
        (And, ac_and);
        (Or, ac_or);
        ( Xor,
          {
            vname = "xor";
            vid = get_id Xor;
            vtype = TFun (TMany TBool, TBool);
            vattrs = [ Builtin ];
          } );
      ]

    let a_opvars =
      [
        ( Concat,
          {
            vname = "++";
            vid = get_id Concat;
            vtype = TFun (TMany (TList TTop), TList TTop);
            vattrs = [ Builtin ];
          } );
      ]
  end

  include T
  module C = Comparable.Make (T)
  include C

  let is_ac (x : t) : bool = List.mem ~equal ac_ops x

  let is_a (x : t) : bool = List.mem ~equal a_ops x

  let is_comp (x : t) : bool = match x with Eq | Lt | Gt | Le | Ge -> true | _ -> false

  let get_ac (x : t) : variable option = List.Assoc.find ~equal ac_opvars x

  let get_a (x : t) : variable option = List.Assoc.find ~equal a_opvars x

  let int_binop (op : t) =
    match op with
    | Times -> Some (fun a b -> a * b)
    | Plus -> Some ( + )
    | Minus -> Some ( - )
    | Max -> Some Caml.max
    | Min -> Some Caml.min
    | Div -> Some ( / )
    | Mod -> Some ( % )
    | _ -> None

  let bool_binop (op : t) = match op with And -> Some ( && ) | Or -> Some ( || ) | _ -> None

  (* | Binop.Impl -> (fun a b -> (not a) || b)
     | Binop.Cons -> (fun a b -> a :: b)
     | Binop.Concat -> (fun a b -> a  @ b) *)
  let comp_op op =
    match op with
    | Eq -> Some Caml.( = )
    | Lt -> Some Caml.( < )
    | Gt -> Some Caml.( > )
    | Le -> Some Caml.( <= )
    | Ge -> Some Caml.( >= )
    | _ -> None
end

module Unop = struct
  module T = struct
    type t = unop [@@deriving sexp]

    let get_id (op : t) : int =
      match op with
      | Id -> 29
      | Neg -> 30
      | Not -> 31
      | Hd -> 32
      | Tl -> 33
      | Abs -> 34
      | IsEmpty -> 35
      | Take _ -> 36
      | UChoice _ -> 37

    let compare b1 b2 = compare (get_id b1) (get_id b2)
  end

  include T
  include Comparable.Make (T)

  let bool_op (op : t) = match op with Not -> Some not | _ -> None

  let int_op (op : t) = match op with Neg -> Some (fun a -> -a) | Abs -> Some abs | _ -> None
end

(* ======================================== *)

module Constant = struct
  module T = struct
    type t = constant [@@deriving sexp]

    let compare = Poly.compare
  end

  include T
  module C = Comparable.Make (T)
  include C

  module Infix : Comparable.Infix with type t := t = C

  include Infix
end

(* Expressions *)

let mk_term ?(attributes = []) ?(ttyp = None) (e : expr) : term =
  match ttyp with
  | Some tp -> { texpr = e; ttyp = tp; tattrs = attributes }
  | None ->
      let attrs =
        if List.exists attributes ~f:(fun x -> Poly.(x = Untyped)) then attributes
        else attributes @ [ Untyped ]
      in
      { texpr = e; ttyp = TTop; tattrs = attrs }

let mk_var ?(not_fresh = false) ?(attributes = []) ?(name = "x") (vtype : typ) =
  let vname = if not_fresh then name else Alpha.get_new_name name in
  let vid = Alpha.get_new_id () in
  { vname; vid; vtype; vattrs = attributes }

let var_of (t : term) = match t.texpr with EVar (Var v) -> Some v | _ -> None

let is_var (t : term) = match t.texpr with EVar (Var _) -> true | _ -> false

let var_of_exn (t : term) =
  match t.texpr with EVar (Var v) -> v | _ -> failhere Caml.__FILE__ "var_of" "Variable expected."

(* Special vars *)
let _INT_MIN = { vname = "INT_MIN"; vid = 40; vtype = TInt; vattrs = [ Builtin ] }

let _INT_MAX = { vname = "INT_MAX"; vid = 41; vtype = TInt; vattrs = [ Builtin ] }

let _HOLE_ = { vname = "??"; vid = 42; vtype = TInt; vattrs = [ Builtin ] }

let _RANGE_ =
  {
    vname = "range";
    vid = 43;
    vtype = TFun (TTup [ TInt; TInt ], TList TInt);
    vattrs = [ Builtin ];
  }

let _PARTITION_ =
  {
    vname = "partition";
    vid = 44;
    vtype = TFun (TTup [ TFun (TTop, TBool); TList TTop ], TTup [ TList TTop; TList TTop ]);
    vattrs = [ Builtin ];
  }

let _TAKE_ =
  {
    vname = "take";
    vid = 45;
    vtype = TFun (TTup [ TList TTop; TInt ], TList TTop);
    vattrs = [ Builtin ];
  }

let _DROP_ =
  {
    vname = "drop";
    vid = 46;
    vtype = TFun (TTup [ TList TTop; TInt ], TList TTop);
    vattrs = [ Builtin ];
  }

let is_min_int t =
  match t.texpr with
  | EVar (Var v) -> Variable.(v = _INT_MIN)
  | EConst (CInt i) -> i = -int_range
  | _ -> false

let is_max_int t =
  match t.texpr with
  | EVar (Var v) -> Variable.(v = _INT_MAX)
  | EConst (CInt i) -> i = int_range
  | _ -> false

let builtin_varname = function
  | "INT_MIN" -> Some _INT_MIN
  | "INT_MAX" -> Some _INT_MAX
  | "??" -> Some _HOLE_
  | "range" -> Some _RANGE_
  | "take" -> Some _TAKE_
  | "drop" -> Some _DROP_
  | _ -> None

(* Term properties *)
let rec is_positive (t : term) =
  match t.texpr with
  | EConst (CInt i) -> i >= 0
  | EBin (Plus, e1, e2) -> is_positive e1 && is_positive e2
  | EBin (Minus, e1, e2) -> is_positive e1 && is_negative e2
  | _ -> false

and is_negative (t : term) =
  match t.texpr with
  | EConst (CInt i) -> i <= 0
  | EBin (Plus, e1, e2) -> is_negative e1 && is_negative e2
  | EBin (Minus, e1, e2) -> is_negative e1 && is_positive e2
  | _ -> false

(** A term is typed if it does not has the Untyped attribute. *)
let is_typed (t : term) = not (List.exists t.tattrs ~f:(fun x -> Poly.(x = Untyped)))

let is_true (t : term) = match t.texpr with EConst (CBool true) -> true | _ -> false

let is_false (t : term) = match t.texpr with EConst (CBool false) -> true | _ -> false

let is_cond (t : term) = match t.texpr with EIte _ -> true | _ -> false

let is_choice (t : term) = match t.texpr with EChoice _ -> true | _ -> false

let has_attr (a : attribute) (t : term) = List.exists t.tattrs ~f:(fun x -> Poly.(x = a))

let has_attr_kind (a : attribute -> bool) (t : term) = List.exists t.tattrs ~f:(fun x -> a x)

let add_attr (a : attribute) (t : term) =
  if has_attr a t then t else { t with tattrs = a :: t.tattrs }

let rem_attr (t : term) (a : attribute) = { t with tattrs = ListTools.remove_elt a t.tattrs }

let rem_attr_kind (t : term) (a : attribute -> bool) =
  { t with tattrs = List.filter ~f:(fun x -> not (a x)) t.tattrs }

let texprs (tl : term list) = List.map ~f:(fun t -> t.texpr) tl

(* ============================================================================================= *)
(*                                 TYPE INFERENCE                                                *)
(* ============================================================================================= *)

let rec type_of_binop_res ((t1, t2) : typ * typ) (op : Binop.t) (e : expr) :
    (typ, string * typ * expr) Result.t =
  match op with
  | Plus -> (
      match (t1, t2) with
      | TInt, TInt -> Ok TInt
      | TList t, TList t' ->
          if ETypes.(t = t') then Ok (TList t) else Error ("concat_diff_types", TList t', e)
      | TList _, _ | _, TList _ -> Error ("concat_nonlist_types", t1, e)
      | _, _ -> Error ("arith_op", TInt, e))
  | Times | Minus | Max | Min | Div | Mod ->
      if ETypes.(t1 = TInt && t2 = TInt) then Ok TInt else Error ("arith_op", TInt, e)
  | And | Or | Xor | Impl ->
      if ETypes.(t1 = TBool && t2 = TBool) then Ok TBool else Error ("bool_op", TBool, e)
  | Cons -> (
      match (t1, t2) with
      | TList t', t when ETypes.(t = t') -> Ok (TList t)
      | _ -> Error ("cons", TList t1, e))
  | Concat -> (
      match (t1, t2) with
      | TList t, TList t' when ETypes.(t = t') -> Ok (TList t)
      | TList TTop, TList t -> Ok (TList t)
      | TList t, TList TTop -> Ok (TList t)
      | _ -> Error ("concat", TTup [ t1; t2 ], e))
  | Eq -> if ETypes.(t1 = t2) then Ok TBool else Error ("eq_op", t1, e)
  | Lt | Gt | Le | Ge ->
      if ETypes.(t1 = TInt && t2 = TInt) then Ok TBool else Error ("comp_op", TTup [ t1; t2 ], e)
  | BChoice binops -> (
      let x = List.map ~f:(fun op' -> type_of_binop_res (t1, t2) op' e) binops in
      match Result.combine_errors x with Ok (hd :: _) -> Ok hd | _ -> Error ("choice_op", t1, e))
  | At -> ( match (t1, t2) with TList t, TInt -> Ok t | _, _ -> Error ("at_accessor", t1, e))

let rec type_of_unop (t : typ) (op : Unop.t) (e : expr) : (typ, string * typ * expr) Result.t =
  match op with
  | Id -> Ok t
  | Neg -> if ETypes.(t = TInt) then Ok TInt else Error ("neg", TInt, e)
  | Not -> if ETypes.(t = TBool) then Ok TBool else Error ("not", TBool, e)
  | Abs -> if ETypes.(t = TInt) then Ok TInt else Error ("abs", TInt, e)
  | IsEmpty -> ( match t with TList _ -> Ok TBool | _ -> Error ("take", TList TTop, e))
  | Hd | Tl -> ( match t with TList t -> Ok t | _ -> Error ("hd/tl", TList TTop, e))
  | Take _ -> ( match t with TList t -> Ok (TList t) | _ -> Error ("take", TList TTop, e))
  | UChoice unops -> (
      let x = List.map ~f:(fun op' -> type_of_unop t op' e) unops in
      match Result.combine_errors x with Ok (hd :: _) -> Ok hd | _ -> Error ("choice_op", t, e))

let type_of_const (c : Constant.t) : typ =
  match c with CInt _ -> TInt | CBool _ -> TBool | CEmpty -> TList TTop | CNone -> TTop

let rec type_term (t : term) : (term, string * typ * expr) Result.t =
  if is_typed t && not ETypes.(t.ttyp = TTop) then Ok t
  else
    match type_of_expr t.texpr with
    | Ok x -> Ok (rem_attr { t with ttyp = x } Untyped)
    | Error e -> Error e

and type_of (t : term) : (typ, string * typ * expr) Result.t =
  match type_term t with Ok t' -> Ok t'.ttyp | Error (s, t, e) -> Error (s, t, e)

and type_of_expr (e : expr) : (typ, string * typ * expr) Result.t =
  let for_funcs argst targs tres =
    match List.zip targs argst with
    | List.Or_unequal_lengths.Ok tl ->
        if List.for_all ~f:(fun (a, b) -> ETypes.(a = b)) tl then tres
        else Error ("args-match", TTup targs, e)
    | _ -> Error ("args-len", TTup targs, e)
  in
  match e with
  | EEmpty -> Ok TTop
  | EVar (Var v) -> Ok v.vtype
  | EHole (t, _) -> Ok t
  | EConst c -> Ok (type_of_const c)
  | EBin (op, t1, t2) ->
      Result.(
        type_of t2 >>= fun x ->
        type_of t1 >>= fun y -> type_of_binop_res (y, x) op e)
  | EUn (op, t) -> Result.(type_of t >>= fun x -> type_of_unop x op e)
  | EIte (c, t1, t2) -> (
      match type_of c with
      | Ok x ->
          if ETypes.(x = TBool) then
            Result.(
              type_of t1 >>= fun x ->
              type_of t2 >>= fun y ->
              match Typ.type_unify x y with
              | Some t -> Ok t
              | None -> Error ("if_branches_diff", TTup [ x; y ], t2.texpr))
          else Error ("if-cond", TBool, c.texpr)
      | _ as e -> e)
  | ESetL (l, i, t) -> (
      Result.(
        type_of l >>= fun x ->
        type_of i >>= fun y ->
        type_of t >>= fun z ->
        match (x, y, z) with
        | TList t1, TInt, t1' ->
            if ETypes.(t1 = t1') then Ok (TList t1)
            else Error ("Set list type no match", TTup [ x; z ], e)
        | _ -> Error ("Set not on list", TTup [ x; y; z ], e)))
  | EWith (struc, mem, t) -> (
      Result.(
        type_of struc >>= fun x ->
        type_of t >>= fun y ->
        match x with
        | TStruct (name, _) -> (
            match Structs.field_type name mem with
            | Some tmem -> if ETypes.(tmem = y) then Ok x else Error ("with", x, struc.texpr)
            | None -> Error ("with", x, struc.texpr))
        | _ -> Error ("with", TTup [ x; y ], e)))
  | EApp (f, args) -> (
      Result.(
        type_of f >>= fun tf ->
        match combine_errors (List.map ~f:type_of args) with
        | Ok argst -> (
            match tf with
            | TFun (TTup targs, tres) -> for_funcs argst targs (Ok tres)
            | TFun (TMany t1, tres) ->
                if List.for_all ~f:(fun at -> ETypes.(at = t1)) argst then Ok tres
                else Error ("args-many", t1, EList args)
            | TFun (t1, tres) -> for_funcs argst [ t1 ] (Ok tres)
            | _ -> Error ("app-args", tf, e))
        | Error lt ->
            let _, ts, _ = List.unzip3 lt in
            Error ("args-match", TTup ts, e)))
  | ETuple el -> (
      Result.(
        match combine_errors (List.map ~f:type_of el) with
        | Ok tl -> Ok (TTup tl)
        | Error tl -> Error ("tuple", TTup (List.map ~f:snd3 tl), e)))
  | EStruct mems -> (
      let memt =
        Result.(
          combine_errors
            (List.map
               ~f:(fun (s, trm) -> match type_of trm with Ok t -> Ok (s, t) | Error e -> Error e)
               mems))
      in
      match memt with
      | Error ml -> Error (String.concat (List.map ~f:fst3 ml), TTup (List.map ~f:snd3 ml), e)
      | Ok x -> (
          match Structs.type_of_fields x with
          | Some y -> Ok y
          | None -> Error ("struct-mems", TTup (List.map ~f:snd x), e)))
  | EMemStruct (sname, memname, _) -> (
      match Structs.field_type sname memname with
      | Some t -> Ok t
      | None -> Error ("struct-mem", TTop, e))
  | EList el -> (
      match el with
      | [] -> Ok (TList TTop)
      | hd :: tl ->
          Result.(
            type_of hd >>= fun thd ->
            if
              List.for_all tl ~f:(fun elt ->
                  match type_of elt with Ok x -> ETypes.(thd = x) | Error _ -> false)
            then Ok (mk_seq_typ thd)
            else Error ("list", thd, e)))
  | EChoice el -> (
      match el with
      | [] -> Ok TTop
      | hd :: tl ->
          Result.(
            type_of hd >>= fun thd ->
            if
              List.for_all tl ~f:(fun elt ->
                  match type_of elt with
                  | Ok x -> Option.is_some (type_unify thd x)
                  | Error _ -> false)
            then Ok thd
            else Error ("choice", thd, e)))
  | EMem (tuple, i) -> (
      match type_of tuple with
      | Ok x -> (
          match x with
          | TTup types -> (
              match List.nth types i with Some t -> Ok t | None -> Error ("mem", TTup types, e))
          | TList t1 -> Ok t1
          | _ -> Error ("Tuple term not tuple typed.", x, e))
      | Error (s, t, e) -> Error (s, t, e))
  | ELambda (vl, body) -> (
      Result.(
        type_of body >>= fun ret ->
        match vl with
        | [ v ] -> Ok (TFun (v.vtype, ret))
        | _ -> Ok (TFun (TTup (List.map ~f:(fun v -> v.vtype) vl), ret))))
  | EFoldL (f, init, el) | EFoldR (f, init, el) -> (
      Result.(
        type_of el >>= fun tel ->
        type_of f >>= fun tf ->
        type_of init >>= fun tinit ->
        match (tf, tinit, tel) with
        | TFun (targs, tres), t0, TList ta -> (
            match targs with
            | TTup [ telt; taccum ] -> (
                match type_unify t0 taccum with
                | Some _ -> (
                    match type_unify t0 tres with
                    | Some _ ->
                        if ETypes.(ta = telt) then Ok tres
                        else Error ("fold-elt", TTup [ ta; telt ], e)
                    | None -> Error ("fold-res", TTup [ t0; tres ], e))
                | None -> Error ("fold-accum", TTup [ t0; taccum ], e))
            | _ -> Error ("fold-args", targs, e))
        | _ -> Error ("fold-lam", TTup [ tf; tel ], e)))
  | ELet (Var v, e1, e2) ->
      Result.(
        type_of e1 >>= fun t1 ->
        if ETypes.(v.vtype = t1) then type_of e2 else Error ("let", v.vtype, e))
  | ELetValues (vars, e1, e2) ->
      let tuplet = TTup (List.map vars ~f:(fun v -> v.vtype)) in
      Result.(
        type_of e1 >>= fun t1 ->
        if ETypes.(tuplet = t1) then type_of e2 else Error ("let", tuplet, e))
  | EPLet (bindings, e2) -> (
      let f (Var x, e) =
        match type_of e with
        | Ok te ->
            if ETypes.(te = x.vtype) then Ok te
            else Error ("Expression bound to wrong variable type", x.vtype, e.texpr)
        | x -> x
      in
      match Result.combine_errors (List.map ~f bindings) with
      | Ok _ -> type_of e2
      | Error _ -> Error ("let-bindings", TTop, e2.texpr))

let is_bool _t = match type_of _t with Ok TBool -> true | _ -> false

let is_int _t = match type_of _t with Ok TInt -> true | _ -> false

(* ============================================================================================= *)
(*                                 TERM BUILDING                                                 *)
(* ============================================================================================= *)
let mk_vt v = mk_term ~ttyp:(Some v.vtype) (EVar (Var v))

let mk_let (lhv : lhvar) (t : term) (t' : term) =
  { texpr = ELet (lhv, t, t'); ttyp = TTop; tattrs = [ Untyped ] }

let mk_let_values (vars : variable list) (t : term) (t' : term) =
  { texpr = ELetValues (vars, t, t'); ttyp = TTop; tattrs = [ Untyped ] }

let mk_tuple (tl : term list) = { texpr = ETuple tl; ttyp = TTup []; tattrs = [ Untyped ] }

let mk_list (tl : term list) = { texpr = EList tl; ttyp = TTup []; tattrs = [ Untyped ] }

let mk_choice (tl : term list) =
  match tl with
  | [] -> type_term { texpr = EChoice []; ttyp = TInt; tattrs = [] }
  | [ a ] -> type_term a
  | _ -> type_term { texpr = EChoice tl; ttyp = TTop; tattrs = [] }

let mk_choice_exn (tl : term list) =
  let res =
    match tl with
    | [ a ] -> type_term a
    | _ -> type_term { texpr = EChoice tl; ttyp = TTop; tattrs = [] }
  in
  match res with Ok r -> r | Error (s, t, _) -> failwith Fmt.(str "%s not of type %a" s pp_typ t)

let mk_app (f : term) (args : term list) =
  { texpr = EApp (f, args); ttyp = TTop; tattrs = [ Untyped ] }

let mk_lambda (args : variable list) (body : term) =
  { texpr = ELambda (args, body); ttyp = TTop; tattrs = [ Untyped ] }

let mk_mem t i = { texpr = EMem (t, i); ttyp = TTop; tattrs = [ Untyped ] }

let mk_struct_mem ~s n t =
  match Structs.field_type s n with
  | Some tmem -> { texpr = EMemStruct (s, n, t); ttyp = tmem; tattrs = [] }
  | None ->
      Log.error Fmt.(printer2_msg "Struct (%a-%a ...)" string s string n);
      (match Structs.get s with
      | Some t -> Log.error (printer_msg "The struct type is: %a." pp_typ t)
      | None -> Log.error (wrap "There is no such struct type."));
      failwith "mk_struct_mem with undeclared struct"

let mk_struct mems =
  let t = { texpr = EStruct mems; ttyp = TTop; tattrs = [] } in
  match type_term t with
  | Ok x -> x
  | Error (s, typ, _) ->
      Log.error (fun f () ->
          Fmt.(pf f "mk_struct (%a)" (list ~sep:comma string) (ListTools.lfst mems)));
      Log.error (fun f () -> Fmt.(pf f "Message: %s." s));
      Log.error (fun f () -> Fmt.(pf f "Type: %a." pp_typ typ));
      failwith "Error typing struct on creation"

let mk_with struc mem mem_expr =
  let t = mk_term (EWith (struc, mem, mem_expr)) in
  match type_term t with
  | Ok t -> t
  | Error (s, _, _) ->
      Fmt.(pf stdout "[ERROR] %s" s);
      failwith "mk_with not a struct"

let mk_set_l a i e =
  let t = mk_term (ESetL (a, i, e)) in
  match type_term t with
  | Ok t -> t
  | Error (s, _, _) ->
      Fmt.(pf stdout "[ERROR] %s" s);
      failwith "mk_set_l not a list"

let mk_foldl ~(f : term) ~(init : term) (el : term) =
  let t = { texpr = EFoldL (f, init, el); ttyp = TTop; tattrs = [ Untyped ] } in
  match type_term t with
  | Ok t -> t
  | Error (s, t, _) -> failwith Fmt.(str "Type error when mk_foldl: %s, %a" s pp_typ t)

let mk_foldr ~(f : term) ~(init : term) (el : term) =
  let t = { texpr = EFoldR (f, init, el); ttyp = TTop; tattrs = [ Untyped ] } in
  match type_term t with
  | Ok t -> t
  | Error (s, t, _) -> failwith Fmt.(str "Type error when mk_foldr: %s, %a" s pp_typ t)

let mk_bin (t1 : term) (op : Binop.t) (t2 : term) =
  { texpr = EBin (op, t1, t2); ttyp = TTop; tattrs = [ Untyped ] }

let mk_un (u : Unop.t) (t : term) = { texpr = EUn (u, t); ttyp = TTop; tattrs = [ Untyped ] }

let mk_opp (t : term) = { texpr = EUn (Neg, t); ttyp = TInt; tattrs = [] }

let mk_add (t1 : term) (t2 : term) = { texpr = EBin (Plus, t1, t2); ttyp = TInt; tattrs = [] }

let mk_mul (t1 : term) (t2 : term) = { texpr = EBin (Times, t1, t2); ttyp = TInt; tattrs = [] }

let mk_sub (t1 : term) (t2 : term) = { texpr = EBin (Minus, t1, t2); ttyp = TInt; tattrs = [] }

let mk_min (t1 : term) (t2 : term) = { texpr = EBin (Min, t1, t2); ttyp = TInt; tattrs = [] }

let mk_max (t1 : term) (t2 : term) = { texpr = EBin (Max, t1, t2); ttyp = TInt; tattrs = [] }

let mk_not (t : term) = { texpr = EUn (Not, t); ttyp = TBool; tattrs = [] }

let mk_and (t1 : term) (t2 : term) = { texpr = EBin (And, t1, t2); ttyp = TBool; tattrs = [] }

let mk_or (t1 : term) (t2 : term) = { texpr = EBin (Or, t1, t2); ttyp = TBool; tattrs = [] }

let mk_cons (t1 : term) (t2 : term) =
  { texpr = EBin (Cons, t1, t2); ttyp = t1.ttyp; tattrs = t1.tattrs }

let mk_hole ?(attrs = []) ((t, i) : typ * int) = { texpr = EHole (t, i); ttyp = t; tattrs = attrs }

let mk_ite c t1 t2 = { texpr = EIte (c, t1, t2); ttyp = TTop; tattrs = [ Untyped ] }

let mk_impl a b = { texpr = EBin (Impl, a, b); ttyp = TBool; tattrs = [] }

let mk_empty_list = { texpr = EConst CEmpty; ttyp = TList TTop; tattrs = [ Untyped ] }

let mk_empty_term = { texpr = EEmpty; ttyp = TTop; tattrs = [] }

let mk_concat (t1 : term) (t2 : term) =
  match (t1.texpr, t2.texpr) with
  | EList tl, EList tl' -> mk_list (tl @ tl')
  | EConst CEmpty, _ -> t2
  | _, EConst CEmpty -> t1
  | _ -> mk_bin t1 Concat t2

let is_empty_term t = match t.texpr with EConst CEmpty -> true | _ -> false

let mk_none = { texpr = EConst CNone; ttyp = TList TTop; tattrs = [ Untyped ] }

let mk_true = { texpr = EConst (CBool true); ttyp = TBool; tattrs = [] }

let mk_false = { texpr = EConst (CBool false); ttyp = TBool; tattrs = [] }

let mk_int i = { texpr = EConst (CInt i); ttyp = TInt; tattrs = [] }

let mk_binop_of_list op t0 t1 tl =
  List.fold_left ~f:(fun t nt -> mk_bin t op nt) ~init:(mk_bin t0 op t1) tl

let mk_binop_of_list_or_fst op li =
  match li with
  | [] -> None
  | [ a ] -> Some a
  | [ a; b ] -> Some (mk_bin a op b)
  | a :: b :: tl -> Some (mk_binop_of_list op a b tl)

let mk_conj (tl : term list) =
  match tl with [] -> mk_true | [ a ] -> a | a :: b :: tl -> mk_binop_of_list And a b tl

let mk_disj (tl : term list) =
  match tl with [] -> mk_false | [ a ] -> a | a :: b :: tl -> mk_binop_of_list Or a b tl

let mk_field_map (t : term) =
  match t.texpr with
  | EStruct fields -> Map.of_alist_exn (module String) fields
  | _ -> Map.empty (module String)

let rec project (t : typ) (t0 : term) : term list =
  if ETypes.equal t0.ttyp t then [ t0 ]
  else
    match (t0.ttyp, t) with
    | TStruct (s, fields), (TInt | TBool) ->
        let f (com, _) = project t (mk_struct_mem ~s com t0) in
        List.concat (List.map ~f fields)
    | _ -> []

let rec project_li (t0 : term) =
  match t0.ttyp with
  | TList _ -> [ t0 ]
  | _ -> (
      match t0.ttyp with
      | TStruct (s, fields) ->
          let f (com, _) = project_li (mk_struct_mem ~s com t0) in
          List.concat (List.map ~f fields)
      | _ -> [])

let get_root_binop (t : term) = match t.texpr with EBin (op, _, _) -> Some op | _ -> None

(* ============================================================================================= *)
(*                                 TERM TRANSFORMER                                              *)
(* ============================================================================================= *)

module Transform = struct
  type transformer = (term -> term) -> term -> term option
  (**
     Generic transformer: when select is true, use transformer to modify the expression tree.
     Otherwise recursively descend in the expression tree.
     The transformer mutate takes as argument the recursive function itself fo that you don't
     have to define all the recursive branches in the mutate function, but you can just reuse
     the rcall function.
  *)

  (* Transform with a top-down carried state. *)
  type 'a tatransform = ('a -> term -> term) -> 'a -> term -> term option

  type 'a drecursor = {
    init : 'a;
    join : 'a -> 'a -> 'a;
    case : (int -> term -> 'a) -> int -> term -> 'a option;
  }

  type 'a recursor = { init : 'a; join : 'a -> 'a -> 'a; case : (term -> 'a) -> term -> 'a option }

  type 'a trecursor = {
    init : 'a;
    join : 'a -> 'a -> 'a;
    case : (term -> term * 'a) -> term -> (term * 'a) option;
  }

  type 'a tfold = {
    tfinit : 'a;
    tfjoin : 'a -> 'a -> 'a;
    tfcase : ('a -> term -> 'a * term) -> 'a -> term -> ('a * term) option;
  }

  let transform (trs : transformer) (t : term) =
    let rec rcall t =
      match trs rcall t with
      | Some t' -> t'
      | None ->
          {
            t with
            texpr =
              (match t.texpr with
              | EEmpty -> EEmpty
              | EBin (b, e1, e2) -> EBin (b, rcall e1, rcall e2)
              | EIte (c, et, ef) -> EIte (rcall c, rcall et, rcall ef)
              | EUn (u, e1) -> EUn (u, rcall e1)
              | ETuple el -> ETuple (lc el)
              | EList el -> EList (lc el)
              | EChoice el -> EChoice (lc el)
              | EMem (e, i) -> EMem (rcall e, i)
              | ELambda (args, body) -> ELambda (args, rcall body)
              | EApp (f, el) -> EApp (rcall f, lc el)
              | EStruct mems -> EStruct (List.map ~f:(fun (s, t) -> (s, rcall t)) mems)
              | EMemStruct (s, m, te) -> EMemStruct (s, m, rcall te)
              | EFoldL (f, e0, le) -> EFoldL (rcall f, rcall e0, rcall le)
              | EFoldR (f, e0, le) -> EFoldR (rcall f, rcall e0, rcall le)
              | ELet (lhv, bind, body) -> ELet (lhv, rcall bind, rcall body)
              | ELetValues (lhv, bind, body) -> ELetValues (lhv, rcall bind, rcall body)
              | EPLet (bindings, body) ->
                  let bindings' = List.map ~f:(fun (x, e) -> (x, rcall e)) bindings in
                  EPLet (bindings', rcall body)
              | EWith (s, mem, x) -> EWith (rcall s, mem, rcall x)
              | ESetL (a, i, e) -> ESetL (rcall a, rcall i, rcall e)
              | EHole _ | EConst _ | EVar _ -> t.texpr);
          }
    and lc = List.map ~f:rcall in
    rcall t

  let rec apply_env (env : term IM.t) (t : term) =
    let rcall t = apply_env env t in
    let lc = List.map ~f:rcall in
    {
      t with
      texpr =
        (match t.texpr with
        | EVar (Var x) -> (
            match Map.find env x.vid with Some replacement -> replacement.texpr | None -> t.texpr)
        | EEmpty -> EEmpty
        | EBin (b, e1, e2) -> EBin (b, rcall e1, rcall e2)
        | EIte (c, et, ef) -> EIte (rcall c, rcall et, rcall ef)
        | EUn (u, e1) -> EUn (u, rcall e1)
        | ETuple el -> ETuple (lc el)
        | EList el -> EList (lc el)
        | EChoice el -> EChoice (lc el)
        | EMem (e, i) -> EMem (rcall e, i)
        | ELambda (args, body) ->
            let new_env =
              List.fold ~init:env
                ~f:(fun accum x -> if Map.mem env x.vid then Map.remove accum x.vid else accum)
                args
            in
            ELambda (args, apply_env new_env body)
        | EApp (f, el) -> EApp (rcall f, lc el)
        | EStruct mems -> EStruct (List.map ~f:(fun (s, t) -> (s, rcall t)) mems)
        | EMemStruct (s, m, te) -> EMemStruct (s, m, rcall te)
        | EFoldL (f, e0, le) -> EFoldL (rcall f, rcall e0, rcall le)
        | EFoldR (f, e0, le) -> EFoldR (rcall f, rcall e0, rcall le)
        | ELet (Var x, e, body) ->
            let e' = rcall e in
            let new_env = if Map.mem env x.vid then Map.remove env x.vid else env in
            ELet (Var x, e', apply_env new_env body)
        | EPLet (bindings, body) ->
            let new_env =
              let f nev (Var x, _) = if Map.mem nev x.vid then Map.remove nev x.vid else nev in
              List.fold ~f ~init:env bindings
            in
            EPLet (List.map ~f:(fun (x, e) -> (x, rcall e)) bindings, apply_env new_env body)
        | EWith (s, mem, x) -> EWith (rcall s, mem, rcall x)
        | ESetL (a, i, e) -> ESetL (rcall a, rcall i, rcall e)
        | ELetValues _ | EHole _ | EConst _ -> t.texpr);
    }

  let apply_rule (rule : term -> term) (t : term) =
    let rec rcall t =
      rule
        {
          t with
          texpr =
            (match t.texpr with
            | EBin (op, e1, e2) -> EBin (op, rcall e1, rcall e2)
            | EIte (c, e1, e2) -> EIte (rcall c, rcall e1, rcall e2)
            | EUn (u, e1) -> EUn (u, rcall e1)
            | EList el -> EList (List.map ~f:rcall el)
            | EChoice el -> EChoice (List.map ~f:rcall el)
            | ETuple el -> ETuple (List.map ~f:rcall el)
            | EStruct mems -> EStruct (List.map ~f:(fun (mn, mt) -> (mn, rcall mt)) mems)
            | EMem (e1, i) -> EMem (rcall e1, i)
            | EMemStruct (s, m, i) -> EMemStruct (s, m, rcall i)
            | ELambda (vl, body) -> ELambda (vl, rcall body)
            | EApp (fn, el) -> EApp (rcall fn, List.map ~f:rcall el)
            | ELet (v, ev, er) -> ELet (v, rcall ev, rcall er)
            | EPLet (bindings, er) ->
                EPLet (List.map ~f:(fun (v, ev) -> (v, rcall ev)) bindings, rcall er)
            | ESetL (a, i, e) -> ESetL (rcall a, rcall i, rcall e)
            | EFoldL (f, e0, le) -> EFoldL (rcall f, rcall e0, rcall le)
            | EFoldR (f, e0, le) -> EFoldR (rcall f, rcall e0, rcall le)
            | EWith (struc, memn, memt) -> EWith (rcall struc, memn, rcall memt)
            | ELetValues _ | EEmpty | EConst _ | EVar _ | EHole _ -> t.texpr);
        }
    in
    rcall t

  let apply_top_down_rule (rule : term -> term) (t : term) =
    let rec rcall t =
      let t = rule t in
      {
        t with
        texpr =
          (match t.texpr with
          | EBin (op, e1, e2) -> EBin (op, rcall e1, rcall e2)
          | EIte (c, e1, e2) -> EIte (rcall c, rcall e1, rcall e2)
          | EUn (u, e1) -> EUn (u, rcall e1)
          | EList el -> EList (List.map ~f:rcall el)
          | EChoice el -> EChoice (List.map ~f:rcall el)
          | ETuple el -> ETuple (List.map ~f:rcall el)
          | EStruct mems -> EStruct (List.map ~f:(fun (mn, mt) -> (mn, rcall mt)) mems)
          | EMem (e1, i) -> EMem (rcall e1, i)
          | EMemStruct (s, m, i) -> EMemStruct (s, m, rcall i)
          | ELambda (vl, body) -> ELambda (vl, rcall body)
          | EApp (fn, el) -> EApp (rcall fn, List.map ~f:rcall el)
          | ELet (v, ev, er) -> ELet (v, rcall ev, rcall er)
          | EPLet (bindings, er) ->
              EPLet (List.map ~f:(fun (v, ev) -> (v, rcall ev)) bindings, rcall er)
          | ESetL (a, i, e) -> ESetL (rcall a, rcall i, rcall e)
          | EFoldL (f, e0, le) -> EFoldL (rcall f, rcall e0, rcall le)
          | EFoldR (f, e0, le) -> EFoldR (rcall f, rcall e0, rcall le)
          | EWith (struc, memn, memt) -> EWith (rcall struc, memn, rcall memt)
          | ELetValues _ | EEmpty | EConst _ | EVar _ | EHole _ -> t.texpr);
      }
    in
    rcall t

  let apply_bottom_up_rule (rule : (term -> term) -> term -> term) (t : term) =
    let rec rcall t =
      let texpr' =
        match t.texpr with
        | EBin (op, e1, e2) -> EBin (op, rcall e1, rcall e2)
        | EIte (c, e1, e2) -> EIte (rcall c, rcall e1, rcall e2)
        | EUn (u, e1) -> EUn (u, rcall e1)
        | EList el -> EList (List.map ~f:rcall el)
        | EChoice el -> EChoice (List.map ~f:rcall el)
        | ETuple el -> ETuple (List.map ~f:rcall el)
        | EStruct mems -> EStruct (List.map ~f:(fun (mn, mt) -> (mn, rcall mt)) mems)
        | EMem (e1, i) -> EMem (rcall e1, i)
        | EMemStruct (s, m, i) -> EMemStruct (s, m, rcall i)
        | ELambda (vl, body) -> ELambda (vl, rcall body)
        | EApp (fn, el) -> EApp (rcall fn, List.map ~f:rcall el)
        | ELet (v, ev, er) -> ELet (v, rcall ev, rcall er)
        | EPLet (bindings, er) -> EPLet (List.map ~f:(fun (x, e) -> (x, rcall e)) bindings, rcall er)
        | EFoldL (f, e0, le) -> EFoldL (rcall f, rcall e0, rcall le)
        | EFoldR (f, e0, le) -> EFoldR (rcall f, rcall e0, rcall le)
        | ESetL (a, i, e) -> ESetL (rcall a, rcall i, rcall e)
        | EWith (struc, memn, memt) -> EWith (rcall struc, memn, rcall memt)
        | ELetValues _ | EEmpty | EConst _ | EVar _ | EHole _ -> t.texpr
      in
      rule rcall { t with texpr = texpr' }
    in
    rcall t

  let apply_bottom_up_rules (rules : ((term -> term) -> term -> term) list)
      (cost_compare : term -> term -> int) (t : term) =
    let rec rcall t =
      let t' =
        {
          t with
          texpr =
            (match t.texpr with
            | EBin (op, e1, e2) -> EBin (op, rcall e1, rcall e2)
            | EIte (c, e1, e2) -> EIte (rcall c, rcall e1, rcall e2)
            | ESetL (c, e1, e2) -> ESetL (rcall c, rcall e1, rcall e2)
            | EUn (u, e1) -> EUn (u, rcall e1)
            | ETuple el -> ETuple (List.map ~f:rcall el)
            | EList el -> EList (List.map ~f:rcall el)
            | EChoice el -> EChoice (List.map ~f:rcall el)
            | EMem (e1, i) -> EMem (rcall e1, i)
            | EWith (s, n, b) -> EWith (rcall s, n, rcall b)
            | ELambda (vl, body) -> ELambda (vl, rcall body)
            | EApp (fn, el) -> EApp (rcall fn, List.map ~f:rcall el)
            | EStruct mems -> EStruct (List.map ~f:(fun (s, t) -> (s, rcall t)) mems)
            | EMemStruct (s, m, e) -> EMemStruct (s, m, rcall e)
            | ELet (v, ev, er) -> ELet (v, rcall ev, rcall er)
            | EPLet (bindings, er) ->
                EPLet (List.map ~f:(fun (x, e) -> (x, rcall e)) bindings, rcall er)
            | EFoldL (f, e0, le) -> EFoldL (rcall f, rcall e0, rcall le)
            | EFoldR (f, e0, le) -> EFoldR (rcall f, rcall e0, rcall le)
            | ELetValues _ | EEmpty | EHole _ | EConst _ | EVar _ -> t.texpr);
        }
      in
      let best =
        List.hd (List.sort ~compare:cost_compare (List.map ~f:(fun rule -> rule rcall t') rules))
      in
      O.value ~default:t best
    in
    rcall t

  let recurse (f : 'a recursor) : term -> 'a =
    let rec rcall t =
      match f.case rcall t with
      | Some x -> x
      | None -> (
          match t.texpr with
          | EBin (_, e1, e2) -> f.join (rcall e1) (rcall e2)
          | EIte (c, e1, e2) -> f.join (rcall c) (f.join (rcall e1) (rcall e2))
          | EUn (_, e1) -> rcall e1
          | EChoice el | ETuple el | EList el ->
              List.fold_left ~f:f.join ~init:f.init (List.map ~f:rcall el)
          | EStruct mems -> List.fold_left ~f:f.join ~init:f.init (List.map ~f:(snd --> rcall) mems)
          | EMem (e1, _) -> rcall e1
          | EMemStruct (_, _, m) -> rcall m
          | ELambda (_, body) -> rcall body
          | EApp (fn, el) ->
              f.join (rcall fn) (List.fold_left ~f:f.join ~init:f.init (List.map ~f:rcall el))
          | ELetValues (_, ev, er) | ELet (_, ev, er) -> f.join (rcall ev) (rcall er)
          | EPLet (bindings, er) ->
              f.join
                (List.fold ~f:(fun a (_, e) -> f.join a (rcall e)) ~init:f.init bindings)
                (rcall er)
          | EFoldL (fn, e0, le) -> f.join (rcall fn) (f.join (rcall e0) (rcall le))
          | EFoldR (fn, e0, le) -> f.join (rcall fn) (f.join (rcall e0) (rcall le))
          | ESetL (c, e1, e2) -> f.join (rcall c) (f.join (rcall e1) (rcall e2))
          | EWith (c, _, e2) -> f.join (rcall c) (rcall e2)
          | EConst _ | EHole _ | EEmpty | EVar _ -> f.init)
    in
    rcall

  let drecurse (f : 'a drecursor) : term -> 'a =
    let rec rcall d t =
      match f.case rcall d t with
      | Some x -> x
      | None -> (
          match t.texpr with
          | EBin (_, e1, e2) -> f.join (rcall (d + 1) e1) (rcall (d + 1) e2)
          | EIte (c, e1, e2) ->
              f.join (rcall (d + 1) c) (f.join (rcall (d + 1) e1) (rcall (d + 1) e2))
          | EUn (_, e1) -> rcall (d + 1) e1
          | EChoice el | ETuple el | EList el ->
              List.fold_left ~f:f.join ~init:f.init (List.map ~f:(rcall (d + 1)) el)
          | EMem (e1, _) -> rcall (d + 1) e1
          | ELambda (_, body) -> rcall (d + 1) body
          | EApp (fn, el) ->
              f.join
                (rcall (d + 1) fn)
                (List.fold_left ~f:f.join ~init:f.init (List.map ~f:(rcall (d + 1)) el))
          | ELet (_, ev, er) -> f.join (rcall (d + 1) ev) (rcall (d + 1) er)
          | EFoldL (fn, e0, le) ->
              f.join (rcall (d + 1) fn) (f.join (rcall (d + 1) e0) (rcall (d + 1) le))
          | EFoldR (fn, e0, le) ->
              f.join (rcall (d + 1) fn) (f.join (rcall (d + 1) e0) (rcall (d + 1) le))
          | EHole _ | EEmpty | EVar _ -> f.init
          | EStruct fields ->
              List.fold_left ~f:f.join ~init:f.init
                (List.map ~f:(fun (_, t) -> rcall (d + 1) t) fields)
          | EMemStruct (_, _, e0) -> rcall d e0
          | EConst _ -> f.init
          | ESetL (a, i, e) -> f.join (f.join (rcall (d + 1) a) (rcall (d + 1) i)) (rcall (d + 1) e)
          | _ -> failwith "drecurse : TODO")
    in
    rcall 0

  let transform_and_recurse (tr : 'a trecursor) (t : term) : term * 'a =
    let rec rcall t =
      match tr.case rcall t with
      | Some x -> x
      | None -> (
          match t.texpr with
          | EBin (b, e1, e2) ->
              let t1', a1 = rcall e1 in
              let t2', a2 = rcall e2 in
              ({ t with texpr = EBin (b, t1', t2') }, tr.join a1 a2)
          | EIte (c, et, ef) ->
              let (c', ac), (et', at), (ef', af) = (rcall c, rcall et, rcall ef) in
              ({ t with texpr = EIte (c', et', ef') }, tr.join ac (tr.join at af))
          | ESetL (c, et, ef) ->
              let (c', ac), (et', at), (ef', af) = (rcall c, rcall et, rcall ef) in
              ({ t with texpr = ESetL (c', et', ef') }, tr.join ac (tr.join at af))
          | EWith (s, n, b) ->
              let s', a1 = rcall s in
              let b', a2 = rcall b in
              ({ t with texpr = EWith (s', n, b') }, tr.join a1 a2)
          | EUn (u, e1) ->
              let e1', a1 = rcall e1 in
              ({ t with texpr = EUn (u, e1') }, a1)
          | ETuple el ->
              let el', a = lc el in
              ({ t with texpr = ETuple el' }, a)
          | EList el ->
              let el', a = lc el in
              ({ t with texpr = EList el' }, a)
          | EChoice el ->
              let el', a = lc el in
              ({ t with texpr = EChoice el' }, a)
          | EMem (e, i) ->
              let e', a = rcall e in
              ({ t with texpr = EMem (e', i) }, a)
          | ELambda (args, body) ->
              let body', a = rcall body in
              ({ t with texpr = ELambda (args, body') }, a)
          | EApp (f, el) ->
              let (f', af), (el', al) = (rcall f, lc el) in
              ({ t with texpr = EApp (f', el') }, tr.join af al)
          | EStruct mems ->
              let es', r = lc2 mems in
              ({ t with texpr = EStruct es' }, r)
          | EMemStruct (s, n, e) ->
              let e', r = rcall e in
              ({ t with texpr = EMemStruct (s, n, e') }, r)
          | EFoldL (f, e0, le) ->
              let (f', af), (e0', a0), (le', al) = (rcall f, rcall e0, rcall le) in
              ({ t with texpr = EFoldL (f', e0', le') }, tr.join (tr.join af a0) al)
          | EFoldR (f, e0, le) ->
              let (f', af), (e0', a0), (le', al) = (rcall f, rcall e0, rcall le) in
              ({ t with texpr = EFoldR (f', e0', le') }, tr.join (tr.join af a0) al)
          | ELet (lhv, bind, body) ->
              let (bind', ab), (body', a) = (rcall bind, rcall body) in
              ({ t with texpr = ELet (lhv, bind', body') }, tr.join ab a)
          | EPLet (bindings, body) ->
              let bind', ab =
                List.fold ~init:([], tr.init)
                  ~f:(fun (b, x) (v, e) ->
                    let e', x' = rcall e in
                    (b @ [ (v, e') ], tr.join x x'))
                  bindings
              and body', a = rcall body in
              ({ t with texpr = EPLet (bind', body') }, tr.join ab a)
          | ELetValues _ | EEmpty | EHole _ | EConst _ | EVar _ -> (t, tr.init))
    and lc =
      List.fold_left
        ~f:(fun (el, a0) e ->
          let e', a = rcall e in
          (el @ [ e' ], tr.join a0 a))
        ~init:([], tr.init)
    and lc2 =
      List.fold_left
        ~f:(fun (el, a0) (s, e) ->
          let e', a = rcall e in
          (el @ [ (s, e') ], tr.join a0 a))
        ~init:([], tr.init)
    in
    rcall t

  let term_fold (tr : 'a tfold) (a : 'a) (t : term) : 'a * term =
    let rec rcall a t =
      match tr.tfcase rcall a t with
      | Some x -> x
      | None -> (
          match t.texpr with
          | EBin (b, e1, e2) ->
              let a1, t1 = rcall a e1 in
              let a2, t2 = rcall a e2 in
              ({ t with texpr = EBin (b, t1, t2) }, tr.tfjoin a1 a2)
          | EIte (c, et, ef) ->
              let (ac, c'), (at, et'), (af, ef') = (rcall a c, rcall a et, rcall a ef) in
              ({ t with texpr = EIte (c', et', ef') }, tr.tfjoin ac (tr.tfjoin at af))
          | ESetL (c, et, ef) ->
              let (ac, c'), (at, et'), (af, ef') = (rcall a c, rcall a et, rcall a ef) in
              ({ t with texpr = ESetL (c', et', ef') }, tr.tfjoin ac (tr.tfjoin at af))
          | EWith (s, n, b) ->
              let s', a1 = rcall a s in
              let b', a2 = rcall a b in
              ({ t with texpr = EWith (s', n, b') }, tr.tfjoin a1 a2)
          | EUn (u, e1) ->
              let a1, e1' = rcall a e1 in
              ({ t with texpr = EUn (u, e1') }, a1)
          | ETuple el ->
              let a, el' = lc a el in
              ({ t with texpr = ETuple el' }, a)
          | EList el ->
              let a, el' = lc a el in
              ({ t with texpr = EList el' }, a)
          | EChoice el ->
              let a, el' = lc a el in
              ({ t with texpr = EChoice el' }, a)
          | EMem (e, i) ->
              let a, e' = rcall a e in
              ({ t with texpr = EMem (e', i) }, a)
          | ELambda (args, body) ->
              let a, body' = rcall a body in
              ({ t with texpr = ELambda (args, body') }, a)
          | EApp (f, el) ->
              let (af, f'), (al, el') = (rcall a f, lc a el) in
              ({ t with texpr = EApp (f', el') }, tr.tfjoin af al)
          | EStruct mems ->
              let r, es' = lc2 a mems in
              ({ t with texpr = EStruct es' }, r)
          | EMemStruct (s, n, e) ->
              let r, e' = rcall a e in
              ({ t with texpr = EMemStruct (s, n, e') }, r)
          | EFoldL (f, e0, le) ->
              let (af, f'), (a0, e0'), (al, le') = (rcall a f, rcall a e0, rcall a le) in
              ({ t with texpr = EFoldL (f', e0', le') }, tr.tfjoin (tr.tfjoin af a0) al)
          | EFoldR (f, e0, le) ->
              let (af, f'), (a0, e0'), (al, le') = (rcall a f, rcall a e0, rcall a le) in
              ({ t with texpr = EFoldR (f', e0', le') }, tr.tfjoin (tr.tfjoin af a0) al)
          | ELet (lhv, bind, body) ->
              let (ab, bind'), (a, body') = (rcall a bind, rcall a body) in
              ({ t with texpr = ELet (lhv, bind', body') }, tr.tfjoin ab a)
          | EPLet (bindings, body) ->
              let bind', ab =
                List.fold ~init:([], tr.tfinit)
                  ~f:(fun (b, x) (v, e) ->
                    let x', e' = rcall a e in
                    (b @ [ (v, e') ], tr.tfjoin x x'))
                  bindings
              and body', a = rcall a body in
              ({ t with texpr = EPLet (bind', body') }, tr.tfjoin ab a)
          | ELetValues _ | EEmpty | EHole _ | EConst _ | EVar _ -> (t, tr.tfinit))
    and lc a =
      List.fold_left
        ~f:(fun (a0, el) e ->
          let x, e' = rcall a e in
          (tr.tfjoin a0 x, el @ [ e' ]))
        ~init:(tr.tfinit, [])
    and lc2 a =
      List.fold_left
        ~f:(fun (a0, el) (s, e) ->
          let x, e' = rcall a e in
          (tr.tfjoin a0 x, el @ [ (s, e') ]))
        ~init:(tr.tfinit, [])
    in
    rcall a t

  let term_atransform (tr : 'a tatransform) (a : 'a) (t : term) : term =
    let rec rcall a t =
      match tr rcall a t with
      | Some x -> x
      | None -> (
          match t.texpr with
          | EBin (b, e1, e2) ->
              let t1 = rcall a e1 in
              let t2 = rcall a e2 in
              { t with texpr = EBin (b, t1, t2) }
          | EIte (c, et, ef) ->
              let c', et', ef' = (rcall a c, rcall a et, rcall a ef) in
              { t with texpr = EIte (c', et', ef') }
          | ESetL (c, et, ef) ->
              let c', et', ef' = (rcall a c, rcall a et, rcall a ef) in
              { t with texpr = ESetL (c', et', ef') }
          | EWith (s, n, b) ->
              let s' = rcall a s in
              let b' = rcall a b in
              { t with texpr = EWith (s', n, b') }
          | EUn (u, e1) ->
              let e1' = rcall a e1 in
              { t with texpr = EUn (u, e1') }
          | ETuple el ->
              let el' = lc a el in
              { t with texpr = ETuple el' }
          | EList el ->
              let el' = lc a el in
              { t with texpr = EList el' }
          | EChoice el ->
              let el' = lc a el in
              { t with texpr = EChoice el' }
          | EMem (e, i) ->
              let e' = rcall a e in
              { t with texpr = EMem (e', i) }
          | ELambda (args, body) ->
              let body' = rcall a body in
              { t with texpr = ELambda (args, body') }
          | EApp (f, el) ->
              let f', el' = (rcall a f, lc a el) in
              { t with texpr = EApp (f', el') }
          | EStruct mems ->
              let es' = lc2 a mems in
              { t with texpr = EStruct es' }
          | EMemStruct (s, n, e) ->
              let e' = rcall a e in
              { t with texpr = EMemStruct (s, n, e') }
          | EFoldL (f, e0, le) ->
              let f', e0', le' = (rcall a f, rcall a e0, rcall a le) in
              { t with texpr = EFoldL (f', e0', le') }
          | EFoldR (f, e0, le) ->
              let f', e0', le' = (rcall a f, rcall a e0, rcall a le) in
              { t with texpr = EFoldR (f', e0', le') }
          | ELet (lhv, bind, body) ->
              let bind', body' = (rcall a bind, rcall a body) in
              { t with texpr = ELet (lhv, bind', body') }
          | EPLet (bindings, body) ->
              let bind' =
                List.fold ~init:[]
                  ~f:(fun b (v, e) ->
                    let e' = rcall a e in
                    b @ [ (v, e') ])
                  bindings
              and body' = rcall a body in
              { t with texpr = EPLet (bind', body') }
          | ELetValues _ | EEmpty | EHole _ | EConst _ | EVar _ -> t)
    and lc a =
      List.fold_left
        ~f:(fun el e ->
          let e' = rcall a e in
          el @ [ e' ])
        ~init:[]
    and lc2 a =
      List.fold_left
        ~f:(fun el (s, e) ->
          let e' = rcall a e in
          el @ [ (s, e') ])
        ~init:[]
    in
    rcall a t
end

let replace_expr ~(old : term) ~(by : term) : term -> term =
  let trf _ t = if Poly.(t = old) then Some by else None in
  Transform.transform trf

let term_size : term -> int = Transform.recurse { init = 1; join = ( + ); case = (fun _ _ -> None) }

let has_branching : term -> bool =
  Transform.recurse
    { init = false; join = ( || ); case = (fun _ t -> if is_cond t then Some true else None) }

let has_nonlinear : term -> bool =
  Transform.recurse
    {
      init = false;
      join = ( || );
      case =
        (fun _ t ->
          match t.texpr with
          | EBin (op, _, _) -> if Binop.is_nonlinear op then Some true else None
          | _ -> None);
    }

let has_holes : term -> bool =
  Transform.recurse
    {
      init = false;
      join = ( || );
      case =
        (fun _ t ->
          match t.texpr with
          | EBin (BChoice _, _, _) | EUn (UChoice _, _) | EChoice _ | EHole _ -> Some true
          | _ -> None);
    }

let is_constant : term -> bool =
  let case _ c = match c.texpr with EConst _ -> Some true | _ -> None in
  Transform.recurse { init = false; join = ( && ); case }

type value = IntValue of int | BoolValue of bool | NoValue

let eval_const t =
  let case f t =
    match t.texpr with
    | EConst c -> Some (match c with CInt i -> IntValue i | CBool b -> BoolValue b | _ -> NoValue)
    | EIte (c, tt, tf) ->
        let tt_val = f tt and tf_val = f tf in
        let c_val = f c in
        Some
          (match c_val with BoolValue true -> tt_val | BoolValue false -> tf_val | _ -> NoValue)
    | EBin (op, t1, t2) ->
        let t1_val = f t1 and t2_val = f t2 in
        Some
          (match (t1_val, t2_val) with
          | IntValue i1, IntValue i2 -> (
              match Binop.comp_op op with
              | Some cmp -> BoolValue (cmp i1 i2)
              | None -> (
                  match Binop.int_binop op with Some iop -> IntValue (iop i1 i2) | None -> NoValue))
          | BoolValue b1, BoolValue b2 -> (
              match Binop.bool_binop op with Some bop -> BoolValue (bop b1 b2) | None -> NoValue)
          | _ -> NoValue)
    | EUn (op, t1) ->
        Some
          (match f t1 with
          | BoolValue b -> (
              match Unop.bool_op op with Some op -> BoolValue (op b) | None -> NoValue)
          | IntValue i -> (
              match Unop.int_op op with Some op -> IntValue (op i) | None -> NoValue)
          | _ -> NoValue)
    | _ -> None
  in
  let join a _ = a in
  Transform.recurse { init = NoValue; join; case } t

let eval_const_parts (t : term) =
  let trf _ t =
    if is_constant t then
      match eval_const t with
      | BoolValue b -> Some (if b then mk_true else mk_false)
      | IntValue i -> Some (mk_int i)
      | NoValue -> None
    else None
  in
  Transform.transform trf t

let cond_possibilities l0 =
  let addcnd cnd l = List.map ~f:(fun c -> cnd :: c) l in
  let rec f c l =
    match l with hd :: tl -> f (addcnd hd c @ addcnd (mk_term (EUn (Not, hd))) c) tl | [] -> c
  in
  match l0 with hd :: tl -> f [ [ hd ]; [ mk_term (EUn (Not, hd)) ] ] tl | [] -> []

(* ========== Term sets and maps ========== *)
(* Replace old_e by new_e in the expression in_e *)

let bmap_terml_add (bop : Binop.t) (elt : 'a) bmap =
  Map.change bmap bop ~f:(fun bindings -> Some (elt :: O.value ~default:[] bindings))

let thash =
  Transform.recurse
    {
      init = 1;
      join = (fun a b -> a * b);
      case =
        (fun f t ->
          match t.texpr with
          | EBin (op, e1, e2) -> Some (Binop.get_id op + f e1 + f e2)
          | EUn (op, e1) -> Some (Unop.get_id op + f e1)
          | EVar (Var v) -> Some v.vid
          | EConst (CInt i) -> Some (abs i + 1)
          | EConst (CBool b) -> Some (if b then -1 else 1)
          | EConst CEmpty -> Some 0
          | _ -> Some 1);
    }

(* For equality, attributes of terms. *)

module Terms = struct
  module T = struct
    type t = term

    let compare t1 t2 =
      let rec _comp t t' =
        match (t.texpr, t'.texpr) with
        | EVar (Var v1), EVar (Var v2) -> compare v1.vid v2.vid
        | EBin (op, e1, e2), EBin (op', e1', e2') ->
            if Binop.(op = op') then
              let c1 = _comp e1 e1' in
              if c1 = 0 then _comp e2 e2' else c1
            else Binop.compare op op'
        | EIte (c, e1, e2), EIte (c', e1', e2') ->
            let cc = _comp c c' in
            if cc = 0 then
              let c1 = _comp e1 e1' in
              if c1 = 0 then _comp e2 e2' else c1
            else cc
        | EUn (op, e1), EUn (op', e1') ->
            if Unop.(op = op') then _comp e1 e1' else Unop.compare op op'
        | ETuple el, ETuple el' -> List.compare _comp el el'
        | EList el, EList el' -> List.compare _comp el el'
        | EMem (e1, i), EMem (e1', i') ->
            let r = _comp e1 e1' in
            if r = 0 then compare i i' else r
        | EMemStruct (struc1, mem1, t1), EMemStruct (struc2, mem2, t2) ->
            let r1 = String.compare struc1 struc2 in
            let r2 = String.compare mem1 mem2 in
            if r1 = 0 then if r2 = 0 then _comp t1 t2 else r2 else r1
        | EStruct mems, EStruct mems' ->
            List.compare
              (fun (n1, t1) (n2, t2) ->
                let r = String.compare n1 n2 in
                if r = 0 then _comp t1 t2 else r)
              mems mems'
        | ELambda (f, body), ELambda (f', body') ->
            let r = List.compare Variable.compare f f' in
            if r = 0 then _comp body body' else r
        | EApp (fn, el), EApp (fn', el') ->
            let r = _comp fn fn' in
            if r = 0 then List.compare _comp el el' else r
        | ELet (Var x, ev, er), ELet (Var x', ev', er') ->
            let r = Variable.compare x x' in
            if r = 0 then
              let r' = _comp ev ev' in
              if r' = 0 then _comp er er' else r'
            else r
        | EFoldL (fn, e0, le), EFoldL (fn', e0', le') ->
            let cc = _comp fn fn' in
            if cc = 0 then
              let c1 = _comp e0 e0' in
              if c1 = 0 then _comp le le' else c1
            else cc
        | EFoldR (fn, e0, le), EFoldR (fn', e0', le') ->
            let cc = _comp fn fn' in
            if cc = 0 then
              let c1 = _comp e0 e0' in
              if c1 = 0 then _comp le le' else c1
            else cc
        | EConst c, EConst c' -> Constant.compare c c'
        | EWith (struc1, n1, t1), EWith (struc2, n2, t2) ->
            let r1 = _comp struc1 struc2 in
            if r1 = 0 then
              let r2 = String.compare n1 n2 in
              if r2 = 0 then _comp t1 t2 else r2
            else r1
        | ESetL (a1, i1, t1), ESetL (a2, i2, t2) ->
            let r1 = _comp a1 a2 in
            if r1 = 0 then
              let r2 = _comp i1 i2 in
              if r2 = 0 then _comp t1 t2 else r2
            else r1
        | _, _ -> Poly.compare t1 t2
      in
      _comp t1 t2

    let sexp_of_t = sexp_of_term

    let hash = Hashtbl.hash
  end

  include T
  include Comparable.Make (T)

  let from_vs (vs : VarSet.t) = List.map ~f:mk_vt (VarSet.elements vs)
end

module Expressions = struct
  module T = struct
    type t = expr

    let compare x y = Terms.compare (mk_term x) (mk_term y)

    let sexp_of_t = sexp_of_expr

    let hash = Hashtbl.hash
  end

  include T
  include Comparable.Make (T)

  let from_vs (vs : VarSet.t) = List.map ~f:(fun v -> EVar (Var v)) (VarSet.elements vs)
end

let all_subterms_in (t : term) ~(mem : term list) : bool =
  let init = false in
  let join = ( && ) in
  let case f t =
    match t.texpr with
    | EConst _ -> Some false
    | EList [] -> Some false
    | EList [ x ] -> Some (f x)
    | EList (hd :: tl) -> Some (List.fold_left ~f:(fun acc e -> join acc (f e)) ~init:(f hd) tl)
    | ETuple [] -> Some false
    | ETuple [ x ] -> Some (f x)
    | ETuple (hd :: tl) -> Some (List.fold_left ~f:(fun acc e -> join acc (f e)) ~init:(f hd) tl)
    | _ -> if List.mem mem t ~equal:Terms.equal then Some true else None
  in
  Transform.recurse { init; join; case } t

(* Symbolic terms and computation *)
(* Generate symbols *)
type symbolic_define = {
  s_vars : VarSet.t;
  (* Variables of base type / base symbols. *)
  s_define : (variable * term) list;
  (* Define variable *)
  s_variable : variable;
  (* The variable for the expression. *)
  s_term : term; (* Symbolic expression for the type. *)
}

let join_sdefs sd1 sd2 =
  { sd1 with s_vars = sd1.s_vars $|| sd2.s_vars; s_define = sd1.s_define @ sd2.s_define }

let sd_v_declare v =
  {
    s_vars = VarSet.singleton v;
    s_define = [];
    s_variable = v;
    s_term = mk_term ~ttyp:(Some v.vtype) (EVar (Var v));
  }

(* PARAMETER symbolic list length. *)
let rec mk_symb_term ?(name_hint = "") ?(len = 2) (telt : typ) : symbolic_define =
  let fold_mk_symb x (sd, el) t =
    let sd' = mk_symb_term ~name_hint:x t in

    ( { sd with s_vars = sd.s_vars $|| sd'.s_vars; s_define = sd.s_define @ sd'.s_define },
      el @ [ sd'.s_term ] )
  in
  let init_symb x t =
    let sd = mk_symb_term ~name_hint:x t in
    (sd, [ sd.s_term ])
  in
  let sd_decl (x : string) (v : variable) t0 tl wrap =
    let sd, el = List.fold_left ~f:(fold_mk_symb x) ~init:(init_symb x t0) tl in

    { sd with s_define = sd.s_define @ [ (v, wrap el) ]; s_variable = v; s_term = wrap el }
  in
  match telt with
  | TTop -> sd_v_declare (mk_var ~name:(name_hint ^ "e") TTop)
  | TInt -> sd_v_declare (mk_var ~name:(name_hint ^ "a") TInt)
  | TBool -> sd_v_declare (mk_var ~name:(name_hint ^ "b") TBool)
  | TFun _ -> sd_v_declare (mk_var ~name:"f" telt)
  | TList t ->
      let v = mk_var ~name:(name_hint ^ "L") (TList t) in
      sd_decl "l" v t (List.init (len - 1) ~f:(fun _ -> t)) mk_list
  | TTup tl -> (
      let v = mk_var ~name:(name_hint ^ "T") (TTup tl) in
      let sname = if String.equal name_hint "" then "t" else name_hint in
      match tl with
      | thd :: ttl -> sd_decl sname v thd ttl (fun el -> mk_term ~ttyp:(Some (TTup tl)) (ETuple el))
      | [] ->
          Log.error (wrap "Cannot make symbolic expression of empty tuple type.");
          failwith "mk_symb_term")
  | TStruct (s, fieldt) -> (
      let v = mk_var ~name:(name_hint ^ "$" ^ s) (TStruct (s, fieldt)) in
      let sname = if String.equal name_hint "" then "struc" else name_hint in
      match fieldt with
      | thd :: ttl ->
          sd_decl sname v (snd thd) (Utils.ListTools.lsnd ttl) (fun el ->
              mk_term
                ~ttyp:(Some (TStruct (s, fieldt)))
                (*  TODO might throw an exception here *)
                (EStruct (List.map2_exn el fieldt ~f:(fun e (s, _) -> (s, e)))))
      | [] ->
          Log.error (wrap "Cannot make symbolic expression of empty struct type.");
          failwith "mk_symb_term")
  | TMany _ ->
      Log.error (wrap "Cannot make symbolic expression for TMany.");
      failwith "mk_symb_term"
  | _ -> failwith "Not supported"
