open Base
module O = Option
open Base

let int_range = 32767

type typ =
  | TTop
  | TInt
  | TBool
  | TSpec of typ * term
  | TList of typ
  | TMany of typ
  | TTup of typ list
  | TStruct of string * (string * typ) list
  | TFun of typ * typ

and vattribute = Anonymous | Builtin | SetLike

and variable = { vname : string; vid : int; vtype : typ; vattrs : vattribute list }

and binop =
  | Times
  | Plus
  | Minus
  | Max
  | Min
  | Div
  | Mod
  | And
  | Or
  | Xor
  | Impl
  | Cons
  | Concat
  | Eq
  | Lt
  | Gt
  | Le
  | Ge
  | BChoice of binop list
  | At

and unop = Id | Neg | Not | IsEmpty | Hd | Tl | Abs | Take of term | UChoice of unop list

and lhvar = Var of variable [@@deriving sexp]

and constant =
  | CInt of int
  | CBool of bool
  | CNone (* Used as a placeholder in some algorithms. *)
  | CEmpty

and expr =
  | EEmpty
  | EBin of binop * term * term
  | EConst of constant
  | EIte of term * term * term
  | EUn of unop * term
  | EVar of lhvar
  | EHole of typ * int
  | ETuple of term list
  | EList of term list
  | EMem of term * int
  | ELambda of variable list * term
  | EApp of term * term list
  | EStruct of (string * term) list
  | EMemStruct of (string * string * term)  (** EFoldL f, init, list **)
  | EFoldL of term * term * term
  | EFoldR of term * term * term
  | ELet of lhvar * term * term
  | ELetValues of variable list * term * term
  | EPLet of (lhvar * term) list * term
  (* Special terms *)
  | ESetL of term * term * term
  | EChoice of term list
  | EWith of term * string * term
[@@deriving sexp]

and attribute =
  | ConstantTerm
  | FuncAC
  | FuncA
  | Untyped
  | ListNormal
  | Offset of int
  | Computed of int * int

(* Terms: expressions with additional information (type, attributes) *)
and term = { texpr : expr; ttyp : typ; tattrs : attribute list }

let rec sexp_of_typ t =
  match t with
  | TTop -> Sexp.Atom "Top"
  | TInt -> Sexp.Atom "Int"
  | TBool -> Sexp.Atom "Bool"
  | TSpec (t, _) -> sexp_of_typ t
  | TList t -> Sexp.(List [ sexp_of_typ t; Atom "list" ])
  | TTup tl -> Sexp.List (Atom "tuple" :: List.map ~f:sexp_of_typ tl)
  | TMany t -> Sexp.(List [ Atom "many"; sexp_of_typ t ])
  | TStruct (n, mems) ->
      let mems = List.map ~f:(fun (name, t) -> Sexp.(List [ Atom name; sexp_of_typ t ])) mems in
      Sexp.(List [ Atom "struct"; Atom n; List mems ])
  | TFun (tin, tout) -> Sexp.(List [ sexp_of_typ tin; Atom "to"; sexp_of_typ tout ])

let rec typ_of_sexp s =
  Sexp.(
    match s with
    | Atom "Top" -> TTop
    | Atom "Bool" -> TBool
    | Atom "Int" -> TInt
    | List [ Atom "struct"; Atom n; List mems ] ->
        let dem = function
          | List [ Atom n; t ] -> (n, typ_of_sexp t)
          | _ -> failwith "Not a type sexp."
        in
        let mems = List.map ~f:dem mems in
        TStruct (n, mems)
    | List [ s; Atom "list" ] -> TList (typ_of_sexp s)
    | List [ Atom "many"; s ] -> TMany (typ_of_sexp s)
    | List [ sin; Atom "to"; sout ] -> TFun (typ_of_sexp sin, typ_of_sexp sout)
    | List (Atom "tuple" :: sts) -> TTup (List.map ~f:typ_of_sexp sts)
    | _ -> failwith "Not a type sexp.")

let mk_seq_typ t = TList t

let is_list t = match t with TList _ -> true | _ -> false

let mk_fun_typ ta tr = TFun (ta, tr)

let mk_struct_typ ~s comps = TStruct (s, comps)

let mk_tup tl = TTup tl

let rec type_comp (t1 : typ) (t2 : typ) : int =
  if Poly.equal t1 t2 then 0
  else
    match (t1, t2) with
    | TSpec (t1', _), TSpec (t2', _) -> type_comp t1' t2'
    | TList t1', TList t2' -> type_comp t1' t2'
    | TFun (ft1, rt1), TFun (ft2, rt2) ->
        let c = type_comp ft1 ft2 in
        if c = 0 then type_comp rt1 rt2 else c
    | TTup tl1, TTup tl2 -> Utils.ListTools.lexicographic type_comp tl1 tl2
    | TStruct (_, l1), TStruct (_, l2) ->
        let comp_field (nf1, tf1) (nf2, tf2) =
          let c = String.compare nf1 nf2 in
          if c = 0 then type_comp tf1 tf2 else c
        in
        Utils.ListTools.lexicographic comp_field l1 l2
    | TMany t1, TMany t2 -> type_comp t1 t2
    | _, TTop -> 1
    | TTop, _ -> -1
    | _, TBool -> 1
    | TBool, _ -> -1
    | TInt, _ -> 1
    | _, TInt -> 1
    | TMany _, _ -> 1
    | _, TMany _ -> -1
    | TStruct _, _ -> 1
    | _, TStruct _ -> -1
    | TTup _, _ -> 1
    | _, TTup _ -> 1
    | TList _, _ -> 1
    | _, TList _ -> -1
    | TSpec _, _ -> 1
    | _, TSpec _ -> 1

let rec type_unify (t1 : typ) (t2 : typ) : typ option =
  match (t1, t2) with
  | TInt, TInt -> Some TInt
  | TBool, TBool -> Some TBool
  | t, TTop | TTop, t -> Some t
  | TList t1', TList t2' -> O.map (type_unify t1' t2') ~f:mk_seq_typ
  | TFun (ft1, rt1), TFun (ft2, rt2) ->
      O.bind (type_unify ft1 ft2) ~f:(fun ta -> O.map (type_unify rt1 rt2) ~f:(mk_fun_typ ta))
  | TTup tl1, TTup tl2 -> (
      match List.zip tl1 tl2 with
      | List.Or_unequal_lengths.Ok l ->
          let tol = List.map ~f:(fun (t, t') -> type_unify t t') l in
          let mf tlo topt = O.merge tlo (O.map ~f:(fun e -> [ e ]) topt) ~f:( @ ) in
          O.map ~f:mk_tup (List.fold_left ~init:(Some []) ~f:mf tol)
      | List.Or_unequal_lengths.Unequal_lengths -> None )
  | TStruct (s1, tl1), TStruct (s2, tl2) ->
      if String.equal s1 s2 then
        match List.zip tl1 tl2 with
        | List.Or_unequal_lengths.Ok l ->
            let tol =
              List.map
                ~f:(fun ((c1, t), (c2, t')) ->
                  Option.map
                    ~f:(fun t0 -> (c1, t0))
                    (if String.(c1 = c2) then type_unify t t' else None))
                l
            in
            let mf tlo topt = O.merge tlo (O.map ~f:(fun e -> [ e ]) topt) ~f:( @ ) in
            O.map ~f:(mk_struct_typ ~s:s1) (List.fold_left ~init:(Some []) ~f:mf tol)
        | List.Or_unequal_lengths.Unequal_lengths -> None
      else None
  | _ -> if type_comp t1 t2 = 0 then Some t1 else None

let struct_fields_equal l1 l2 =
  let comp_field (nf1, tf1) (nf2, tf2) =
    let c = String.compare nf1 nf2 in
    if c = 0 then match type_unify tf1 tf2 with Some _ -> 0 | None -> type_comp tf1 tf2 else c
  in
  Utils.ListTools.lexicographic comp_field l1 l2 = 0

let struct_name (t : typ) : string option = match t with TStruct (s, _) -> Some s | _ -> None

module ETypes = struct
  module T = struct
    type t = typ

    let compare t1 t2 = type_comp t1 t2

    let sexp_of_t = sexp_of_typ
  end

  include T
  module C = Comparable.Make (T)
  include C

  module Infix : Comparable.Infix with type t := t = C

  include Infix
end

(* ============================================================================================= *)
(* =================================   PRETTY PRINTING TYPES   ================================= *)
(* ============================================================================================= *)

let rec pp_typ (formt : Formatter.t) (t : typ) =
  let unstyled formt t =
    match t with
    | TTop -> Fmt.(string formt "'a")
    | TInt -> Fmt.(string formt "Int")
    | TBool -> Fmt.(string formt "Bool")
    | TSpec (t, _) -> Fmt.(pf formt "(%a @ _)" pp_typ t)
    | TList t -> Fmt.(brackets pp_typ formt t)
    | TMany t -> Fmt.(pf formt "%a ..." pp_typ t)
    | TTup tl -> Fmt.(parens (list ~sep:comma pp_typ) formt tl)
    | TFun (t1, t2) -> Fmt.(pf formt "@[<hov 2>(%a -> %a)@]" pp_typ t1 pp_typ t2)
    | TStruct (n, mems) ->
        Fmt.(
          pf formt "@[%s {%a}@]" n
            (list ~sep:semi (pair ~sep:(fun fmt () -> pf fmt " : ") string pp_typ))
            mems)
  in
  Fmt.(styled `Green unstyled formt t)

let rec pp_typ_short (formt : Formatter.t) (t : typ) =
  let unstyled formt t =
    match t with
    | TTop -> Fmt.(string formt "'a")
    | TInt -> Fmt.(string formt "Int")
    | TBool -> Fmt.(string formt "Bool")
    | TSpec (t, _) -> Fmt.(pf formt "(%a @ _)" pp_typ t)
    | TList t -> Fmt.(brackets pp_typ_short formt t)
    | TMany t -> Fmt.(pf formt "%a ..." pp_typ_short t)
    | TTup tl -> Fmt.(parens (list ~sep:comma pp_typ_short) formt tl)
    | TFun (t1, t2) -> Fmt.(pf formt "(%a -> %a)" pp_typ_short t1 pp_typ_short t2)
    | TStruct (n, _) -> Fmt.(pf formt "%s" n)
  in
  Fmt.(styled `Green unstyled formt t)

let pp_struct_def (formt : Formatter.t) (t : typ) =
  match t with
  | TStruct (s, fields) ->
      Fmt.(
        pf formt "(struct %s (%a) #:transparent)" s (list ~sep:sp string)
          (Utils.ListTools.lfst fields))
  | _ -> ()
