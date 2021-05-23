open Base
open Term
open Typ

module TupleElements = struct
  module T = struct
    type t = variable * int

    let compare (v1, i1) (v2, i2) =
      let c = Variable.compare v1 v2 in
      if c = 0 then compare i1 i2 else c

    let sexp_of_t (v, i) = Sexp.(List [ Variable.sexp_of_t v; sexp_of_int i ])

    let hash (v, i) = v.vid + i
  end

  module C = struct
    type t = T.t

    include Comparable.Make (T)
  end

  module S = Set.M (C)
  include T
  include S

  let empty = Set.empty (module C)

  let singleton = Set.singleton (module C)

  let elements = Set.elements
end

let vars_of (t : term) : VarSet.t =
  Transform.recurse
    {
      init = VarSet.empty;
      join = Set.union;
      case =
        (fun _ _t -> match _t.texpr with EVar (Var v) -> Some (VarSet.singleton v) | _ -> None);
    }
    t

let free_variables (t : term) : VarSet.t =
  let rec f (b, free) t =
    match t.texpr with
    | EVar (Var x) -> (b, if Set.mem b x then free else free $|| VarSet.singleton x)
    | ELet (Var x, e, body) ->
        let _, u' = f (b, free) e in
        f (b $|| VarSet.singleton x, u') body
    | ELetValues (x, e, body) ->
        let _, u' = f (b, free) e in
        f (b $|| VarSet.of_list x, u') body
    | EPLet (bindings, body) ->
        let newbound, frees =
          let f (nb, fr) = function Var v, e -> (Set.add nb v, snd (f (b, fr) e)) in
          List.fold ~f ~init:(b, free) bindings
        in
        f (newbound, frees) body
    | ELambda (args, body) -> f (b $|| VarSet.of_list args, free) body
    | EWith (t1, _, t2) | EBin (_, t1, t2) ->
        let (b1, u1), (b2, u2) = (f (b, free) t1, f (b, free) t2) in
        (b1 $|| b2, u1 $|| u2)
    | EFoldL (t1, t2, t3) | EFoldR (t1, t2, t3) | EIte (t1, t2, t3) | ESetL (t1, t2, t3) ->
        let (b1, u1), (b2, u2), (b3, u3) = (f (b, free) t1, f (b, free) t2, f (b, free) t3) in
        (b1 $|| b2 $|| b3, u1 $|| u2 $|| u3)
    | EApp (a, e) ->
        let b1, u1 = flist (b, free) e in
        let b2, u2 = f (b, free) a in
        (b1 $|| b2, u1 $|| u2)
    | EMemStruct (_, _, t1) | EMem (t1, _) | EUn (_, t1) -> f (b, free) t1
    | EChoice tl | ETuple tl | EList tl -> flist (b, free) tl
    | EStruct mems -> flist (b, free) (Utils.ListTools.lsnd mems)
    | EConst _ | EHole _ | EEmpty -> (b, free)
  and flist (b, u) tl = List.fold ~init:(b, u) ~f tl in
  Set.filter ~f:(fun v -> not (Variable.is_builtin v)) (snd (f VarSet.(empty, empty) t))

let used_structs (t : term) =
  let single t = Set.singleton (module Typ.ETypes) t in
  let init = Set.empty (module Typ.ETypes) in
  let join = Set.union in
  let case f t =
    match t.texpr with
    | EVar (Var v) -> ( match v.vtype with TStruct _ -> Some (single v.vtype) | _ -> Some init )
    | EMemStruct (s, _, t') -> (
        match Structs.get s with
        | Some t -> Some (join (single t) (f t'))
        | None ->
            Utils.failhere Caml.__FILE__ "pp_struct_defs"
              "Unkown struct in program, cannot output sketch." )
    | EStruct mems -> (
        let lt = List.fold ~f:(fun acc (_, t') -> join acc (f t')) ~init mems in
        match type_of t with Ok t -> Some (join lt (single t)) | _ -> None )
    | _ -> None
  in
  Transform.recurse { init; join; case } t

let record_accesses_of (t : term) : TupleElements.t =
  let _oc _ t =
    match t.texpr with
    | EMem (m, i) -> (
        match m.texpr with EVar (Var t) -> Some (TupleElements.singleton (t, i)) | _ -> None )
    | _ -> None
  in
  Transform.recurse { init = TupleElements.empty; join = Set.union; case = _oc } t

let get_conditions =
  let init = Set.empty (module Terms) in
  let join = Set.union in
  let case f t =
    match t.texpr with
    | EIte (c, et, ef) ->
        Some (Set.union_list (module Terms) [ f et; f ef; Set.singleton (module Terms) c ])
    | _ -> None
  in
  Transform.recurse { init; join; case }

(* Small transformation requiring analysis *)
let rec parallelize_lets (t : term) : term =
  let bta_contains bta fv = List.exists ~f:(fun (x, _) -> Set.mem fv x) bta in
  let apply_bta bta t =
    match bta with
    | [ (x, e) ] -> { t with texpr = ELet (Var x, e, t) }
    | bindings -> { t with texpr = EPLet (List.map ~f:(fun (v, e) -> (Var v, e)) bindings, t) }
  in
  let rec successive_lets bta t =
    match t.texpr with
    | ELet (Var x, e, body) ->
        let fv = free_variables e in
        if bta_contains bta fv then
          let t' = parallelize_lets t in
          apply_bta bta t'
        else successive_lets (bta @ [ (x, e) ]) body
    | _ -> apply_bta bta (parallelize_lets t)
  in
  let trf _ t =
    match t.texpr with ELet (Var x, e, body) -> Some (successive_lets [ (x, e) ] body) | _ -> None
  in
  Transform.transform trf t

let num_nested_folds (t : term) =
  let init = 0 in
  let join = ( + ) in
  let case rcall t =
    match t.texpr with EFoldL (f, _, _) | EFoldR (f, _, _) -> Some (rcall f + 1) | _ -> None
  in
  Transform.recurse { init; join; case } t
