open Base
open Typ
open Term
open TermPp
open TermUtils
open AcTerm
open Utils

type cbudget = { n : int; k : int; m : int; c : int }

(* Resource model to measure cost of subterm in term. *)
type resource = RScalar of term | RList of term list [@@deriving sexp]

let pp_resource ?(pretty = false) (frmt : Formatter.t) (r : resource) =
  if pretty then
    match r with
    | RScalar t -> Fmt.(pf frmt "@[<hov 2>Scalar %a@]" pp_term t)
    | RList tl -> Fmt.(pf frmt "@[<hov 2>List [%a]@]" (list ~sep:comma (parens pp_term)) tl)
  else Sexp.pp_hum frmt (sexp_of_resource r)

(* Depth-count cost for normalization. *)
type dc_cost = { max_depth : int; count : int }

(* List normal forms - used in noralization of expressions. *)
let to_list_normal_form : term -> term =
  Transform.transform (fun f t ->
      match t.texpr with
      | EBin (Cons, t1, t2) -> Some (add_attr ListNormal (mk_bin (f t1) Concat (mk_list [ t2 ])))
      | EList terml -> (
          match terml with
          | [] -> Some mk_empty_list
          | [ _ ] -> Some (add_attr ListNormal t)
          | hd :: hd' :: tl ->
              Some
                (add_attr ListNormal
                   (mk_binop_of_list Concat
                      (mk_list [ hd ])
                      (mk_list [ hd' ])
                      (List.map ~f:(fun t -> mk_list [ t ]) tl))) )
      | _ -> None)

let of_list_normal_form : term -> term =
  Transform.transform (fun f t ->
      match t.texpr with
      | EBin (Concat, t1, t2) -> (
          match t2.texpr with
          | EList [ t1_0 ] -> Some (rem_attr (mk_cons (f t1) t1_0) ListNormal)
          | EList [] -> Some (rem_attr (f t1) ListNormal)
          | _ -> None )
      | _ -> None)

let is_list_term_of (t : term) (lt : term list) =
  let is_concat_args args =
    let args' = List.filter ~f:(fun t -> Terms.(not (t = mk_empty_list))) args in
    let args'' =
      List.map
        ~f:(fun m ->
          match m.texpr with
          | EList l -> l
          | EBin (Cons, _, _) -> failwith "Term not in list normal form."
          | _ -> [])
        args'
    in
    List.equal Terms.equal (List.concat args'') lt
  in
  let t = to_ac (if has_attr ListNormal t then t else to_list_normal_form t) in
  match t.texpr with
  | EApp (f_concat, lists) -> (
      match get_op_t f_concat with Some Concat -> is_concat_args lists | _ -> false )
  | EList lt2 -> List.equal Terms.equal lt lt2
  | _ -> false

let terms_of_resources (rl : resource list) : term list =
  let f r = match r with RScalar t -> t | RList tl -> mk_list tl in
  List.map ~f rl

let resources_of_terms (tl : term list) : resource list =
  let f t = match t.texpr with EList tl -> RList tl | _ -> RScalar t in
  List.map ~f tl

let compare_dc_cost c1 c2 =
  let x = compare c1.count c2.count in
  if x = 0 then compare c1.max_depth c2.max_depth else x

let zero_cost = { max_depth = 0; count = 0 }

let resource_cost (resources : resource list) (d : int) (ct : term) : dc_cost option =
  let f res =
    match res with
    | RScalar s -> if ACES.(s = ct) then Some { max_depth = d; count = 1 } else None
    | RList lt ->
        if all_subterms_in ct ~mem:lt then
          if is_list_term_of ct lt then Some { max_depth = d; count = 1 }
          else Some { max_depth = d; count = occurrences ct lt }
        else None
  in
  match List.filter ~f:Option.is_some (List.map ~f resources) with
  | [] -> None
  | somes ->
      List.(last (sort ~compare:compare_dc_cost (map ~f:(Option.value ~default:zero_cost) somes)))

let dc_cost_of_term (resources : resource list) : term -> dc_cost =
  let init = zero_cost in
  let join c1 c2 = { max_depth = max c1.max_depth c2.max_depth; count = c1.count + c2.count } in
  let case _ d t = resource_cost resources d t in
  Transform.drecurse { init; join; case }

let increase_budget (budget : cbudget) : cbudget option =
  (* If default has been specified do not search for another budget. *)
  if !Config.k >= 0 && !Config.m >= 0 && !Config.c >= 0 then None
  else if budget.m < budget.c then Some { budget with m = budget.m + 1 }
  else if budget.k < budget.n then Some { budget with k = budget.k + 1; c = budget.c; m = 2 }
  else if budget.c < !Config.cmax then Some { budget with k = 0; c = budget.c + 1; m = 2 }
  else None
