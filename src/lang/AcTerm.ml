open Term
open Typ
open TermPp
open TermUtils
open Utils
open Base

let norm_assoc = ref true

let ident_elts =
  [
    (Plus, EConst (CInt 0));
    (Times, EConst (CInt 1));
    (Max, EVar (Var _INT_MIN));
    (Min, EVar (Var _INT_MAX));
    (And, EConst (CBool true));
    (Or, EConst (CBool false));
    (Concat, EConst CEmpty);
  ]

let get_op (v : variable) : Binop.t option =
  ListTools.rassoc ~equal:Variable.equal Binop.(a_opvars @ ac_opvars) v

let get_op_t (vt : term) : Binop.t option =
  match vt.texpr with EVar (Var v) -> get_op v | _ -> None

let mk_ac_app bop lt =
  Option.map ~f:(fun x -> mk_term ~attributes:[ FuncAC ] (EApp (mk_vt x, lt))) (Binop.get_ac bop)

let mk_a_app bop lt =
  Option.map ~f:(fun x -> mk_term ~attributes:[ FuncA ] (EApp (mk_vt x, lt))) (Binop.get_a bop)

let has_ident (op : Binop.t) = (Binop.is_a op || Binop.is_ac op) && not Binop.(op = Xor)

let ident_elt (op : Binop.t) = Binop.(List.Assoc.find ~equal ident_elts op)

(**
  `distributes op1 op2` is true when `op1` is distributive over `op2`.
  For example `distributes Plus Max is true.
*)
let distributes (op1 : Binop.t) (op2 : Binop.t) =
  match (op1, op2) with
  | Plus, Max | Plus, Min | Times, Plus | Div, Plus | And, Or -> true
  | _ -> false

let is_idempotent (op : Binop.t) = match op with Max | Min | And | Or -> true | _ -> false

let rec to_ac (t : term) =
  let rec flatten cur_op t =
    match t.texpr with
    | EBin (op, e1, e2) when Binop.(op = cur_op) -> flatten cur_op e1 @ flatten cur_op e2
    | _ -> [ to_ac t ]
  in
  let mutate _ t =
    match t.texpr with
    | EBin (op, e1, e2) when Binop.is_ac op ->
        let operands = flatten op e1 @ flatten op e2 in
        (* In following, failure is a bug in program, clause is guarded by is_ac. *)
        mk_ac_app op operands
    | EBin (op, e1, e2) when Binop.is_a op ->
        let operands = flatten op e1 @ flatten op e2 in
        (* In following, failure is a bug in program, clause is guarded by is_a. *)
        mk_a_app op operands
    | _ -> None
  in
  Transform.transform mutate t

let cond_blast t =
  if has_attr FuncAC t then
    match (to_ac t).texpr with
    | EApp (vf, args) -> (
        match vf.texpr with
        | EVar (Var v) -> ( match get_op v with Some And -> args | _ -> [ t ] )
        | _ -> [ t ] )
    | _ -> [ t ]
  else [ t ]

let not_rule t =
  match t.texpr with
  | EUn (Not, { texpr = EBin (Or, t1, t2); _ }) -> mk_and (mk_not t1) (mk_not t2)
  | EUn (Not, { texpr = EBin (And, t1, t2); _ }) -> mk_or (mk_not t1) (mk_not t2)
  | _ -> t

type term_pair = TPair of term_pair * term_pair | TTerm of term [@@deriving sexp]

let rec pp_term_pair (frmt : Formatter.t) (tp : term_pair) =
  match tp with
  | TPair (t1, t2) -> Fmt.(parens (pair ~sep:comma pp_term_pair pp_term_pair)) frmt (t1, t2)
  | TTerm t -> pp_term frmt t

let to_term_with_op (op : Binop.t) (tp : term_pair) =
  let rec f tp = match tp with TPair (tp1, tp2) -> mk_bin (f tp1) op (f tp2) | TTerm t -> t in
  f tp

let all_assocs (t0 : term) (t1 : term) (tl : term list) =
  let rec g e tp =
    match tp with
    | TTerm t -> [ TPair (TTerm t, TTerm e) ]
    | TPair (tp1, tp2) ->
        [ TPair (tp, TTerm e); TPair (tp1, TPair (tp2, TTerm e)) ]
        @ List.map ~f:(fun _t -> TPair (tp1, _t)) (g e tp2)
  in
  let rec f acc l =
    match l with [] -> acc | hd :: tl -> f (List.concat (List.map ~f:(g hd) acc)) tl
  in
  f [ TPair (TTerm t0, TTerm t1) ] tl

let best_associative_grouping_from_all (compare_cost : term -> term -> int) (op : Binop.t)
    (l0 : term) (l : term list) : term option =
  match l with
  | [] -> Some l0
  | [ x ] -> Some (mk_bin l0 op x)
  | hd :: tl ->
      (* let _ = compare_cost l0 hd in
       * Some (mk_binop_of_list op l0 hd tl) *)
      let x = List.map ~f:(to_term_with_op op) (all_assocs l0 hd tl) in
      Fmt.(pf stdout "List len : %i.@." (List.length x));
      List.hd (List.sort x ~compare:compare_cost)

let rec best_associative_grouping_opt (compare_cost : term -> term -> int) (op : Binop.t)
    (l : term list) : term option =
  let rcall = best_associative_grouping_opt compare_cost op in
  let f (p1, mt, p2) t =
    let c = compare_cost t mt in
    (* if c = 0 then
     *   (if List.length p1 < List.length p2 then
     *      (p1 @ (mt :: p2), t, [])
     *    else
     *      (p1, mt, p2 @ [t]))
     * else *)
    if c >= 0 then (p1 @ (mt :: p2), t, []) else (p1, mt, p2 @ [ t ])
  in
  match l with
  | [] -> None
  | [ x ] -> Some x
  | [ x; y ] -> Some (mk_bin x op y)
  | l0 :: l1 :: tl -> (
      let p1, mt, p2 = List.fold_left ~f ~init:([], l0, []) (l1 :: tl) in
      match (rcall p1, rcall p2) with
      | Some x, Some y ->
          let t1 = mk_bin (mk_bin x op mt) op y in
          let t2 = mk_bin x op (mk_bin mt op y) in
          if compare_cost t1 t2 >= 0 then Some t2 else Some t1
      | None, Some y -> Some (mk_bin mt op y)
      | Some x, None -> Some (mk_bin x op mt)
      | _ -> None )

let rebuild_tree_AC (compare_cost : term -> term -> int) : term -> term =
  let f rfunc t =
    if not (has_attr FuncAC t || has_attr FuncA t) then None
    else
      match t.texpr with
      | EApp (f, args) -> (
          match get_op_t f with
          (* Associative-commutative case. *)
          | Some op when Binop.is_ac op -> (
              let el' = List.map ~f:rfunc args in
              let el_ord = List.sort ~compare:compare_cost el' in
              match el_ord with
              | [ x ] -> Some x
              | hd :: tl ->
                  Some (List.fold_left ~f:(fun tree e -> mk_term (EBin (op, e, tree))) ~init:hd tl)
              | [] ->
                  failhere Caml.__FILE__ "rebuild_tree_AC"
                    "Unexpected length for list in AC conversion." )
          (* Associative case. *)
          | Some op when Binop.is_a op -> (
              let el' = List.map ~f:rfunc args in
              match el' with
              | hd :: tl ->
                  if !norm_assoc then best_associative_grouping_opt compare_cost op (hd :: tl)
                  else
                    Some
                      (List.fold_left ~f:(fun tree e -> mk_term (EBin (op, e, tree))) ~init:hd tl)
              (* | _ ->
               *   (\* General case, the algorithm becomes VERY slow.
               *      Picks the best among all the possible associations. (>> Catalan(n) complexity)!
               *      Never used in current state.
               *   *\)
               *   best_associative_grouping_from_all compare_cost op hd tl) *)
              | [] ->
                  failhere Caml.__FILE__ "rebuild_tree_AC"
                    "Unexpected length for list in AC conversion." )
          | _ -> None )
      | _ -> None
  in
  Transform.transform f

(** Equality under associativity and commutativity. Can be defined
    as structural equality of expressions trees with reordering in flat
    terms *)
let ac_compare t1 t2 : int =
  let rec aux_comp _t1 _t2 =
    match (_t1.texpr, _t2.texpr) with
    | EBin (op1, e11, e12), EBin (op2, e21, e22) when Binop.is_ac op1 && Binop.is_ac op2 ->
        let comp_nonpermut =
          let c1 = Binop.compare op1 op2 in
          if c1 = 0 then
            let c1' = aux_comp e11 e21 in
            if c1' = 0 then aux_comp e12 e22 else c1'
          else c1
        in
        let comp_permut =
          let c2 = Binop.compare op1 op2 in
          if c2 = 0 then
            let c2' = aux_comp e11 e22 in
            if c2' = 0 then aux_comp e12 e21 else c2'
          else c2
        in
        if comp_nonpermut = 0 then comp_nonpermut
        else if comp_permut = 0 then comp_permut
        else comp_nonpermut
    | EUn (op1, e11), EUn (op2, e21) ->
        let c = Unop.compare op1 op2 in
        if c = 0 then aux_comp e11 e21 else c
    | EApp (f1, el1), EApp (f2, el2) ->
        let c = aux_comp f1 f2 in
        if c = 0 then
          match f1.texpr with
          | EVar (Var fn) -> (
              match get_op fn with
              (* When op is associative and commutative. *)
              | Some op when Binop.is_ac op ->
                  let has_elt_eq x el = List.exists ~f:(fun y -> aux_comp y x = 0) el in
                  if
                    Binop.is_ac op
                    && List.length el1 = List.length el2
                    && List.for_all ~f:(fun elt1 -> has_elt_eq elt1 el2) el1
                    && List.for_all ~f:(fun elt2 -> has_elt_eq elt2 el1) el2
                  then 0
                  else List.compare aux_comp el1 el2
              (* Case op is not commutative or just not in ac *)
              | _ -> List.compare aux_comp el1 el2 )
          | _ -> List.compare aux_comp el1 el2
        else c
    | EIte (c1, e11, e12), EIte (c2, e21, e22) ->
        let cc = aux_comp c1 c2 in
        if cc = 0 then
          let c1 = aux_comp e11 e21 in
          if c1 = 0 then aux_comp e12 e22 else c1
        else cc
    | EList el, EList el' | ETuple el, ETuple el' -> List.compare aux_comp el el'
    | EVar (Var v1), EVar (Var v2) -> compare v1.vid v2.vid
    | _, _ -> Terms.compare _t1 _t2
  in
  if is_list_type t1 && is_list_type t2 then
    match (of_list_term t1, of_list_term t2) with
    | Some l1, Some l2 -> List.compare aux_comp l1 l2
    | _, _ -> -1 (* Should not happen since t1 and t2 are of list type. *)
  else aux_comp (to_ac t1) (to_ac t2)

module ACES = struct
  module T = struct
    type t = term

    let compare = ac_compare

    let sexp_of_t = sexp_of_term
  end

  include T
  module C = Comparable.Make (T)
  include C

  include (C : Comparable.Infix with type t := t)
end

let rec replace ~(old : term) ~(by : term) (in_e : term) =
  if ACES.(in_e = old) then by
  else
    let rcall = replace ~old ~by in
    {
      in_e with
      texpr =
        ( match in_e.texpr with
        | EBin (b, e1, e2) -> EBin (b, rcall e1, rcall e2)
        | EIte (c, e1, e2) -> EIte (rcall c, rcall e1, rcall e2)
        | EUn (u, e) -> EUn (u, rcall e)
        | EApp (f, e) -> EApp (rcall f, List.map ~f:rcall e)
        | ELambda (args, e) -> ELambda (args, rcall e)
        | EList e -> EList (List.map ~f:rcall e)
        | EStruct fields -> EStruct (List.map fields ~f:(fun (s, t) -> (s, rcall t)))
        | _ -> in_e.texpr );
    }

let apply_substs_ac (substs : (term * term) list) (t : term) : term =
  List.fold ~f:(fun t (old, by) -> replace ~old ~by t) ~init:t substs

let lambdify (x : variable) (t : term) (body : term) =
  let subs =
    match t.texpr with
    | EVar _ -> [ (t, mk_vt x) ]
    | EStruct mems -> (
        match x.vtype with
        | TStruct (structname, _) ->
            let f (mname, mt) = (mt, mk_struct_mem ~s:structname mname (mk_vt x)) in
            List.map ~f mems
        | TInt ->
            let f (_, mt) = (mt, mk_vt x) in
            List.map ~f mems
        | _ ->
            failwith
              Fmt.(
                str "Lambdify  %a: mismatched types %a and %s:%a." pp_term body pp_term t x.vname
                  pp_typ x.vtype) )
    | _ -> []
  in
  List.fold subs ~f:(fun e (old, by) -> replace ~old ~by e) ~init:body

let rec unify (t1 : term) (t2 : term) : (term * term) list =
  (* let  unify_ac_args args1 args2 =
   *   (\* Remove common arguments *\)
   *   let _, _' = ListTools.remove_intersection ~equal:ACES.equal args1 args2 in
   *   [ e_b true, e_b false]
   * in *)
  let unify_ac t t' = [ (t, t') ] in
  if ACES.(t1 = t2) then []
  else if has_attr FuncAC t1 && has_attr FuncAC t1 then unify_ac t1 t2
  else
    match (t1.texpr, t2.texpr) with
    (* Binary operation, non-commutative *)
    | EBin (b, e1', e2'), EBin (b', e1'', e2'') when Binop.(b = b') ->
        unify e1' e1'' @ unify e2' e2''
    | EUn (u, e1'), EUn (u', e2') when Unop.(u = u') -> unify e1' e2'
    | EIte (c, et, ef), EIte (c', et', ef') ->
        if ACES.(c = t_not c' || t_not c = c') then unify et ef' @ unify ef et'
        else unify c c' @ unify et et' @ unify ef ef'
    | _, _ -> [ (t1, t2) ]

let distrib_neg (t : term) =
  let rule t =
    match t.texpr with
    | EUn (Not, t1) -> (
        match t1.texpr with
        | EUn (Not, t2) -> t2
        | EBin (Or, t1, t2) -> mk_and (mk_not t1) (mk_not t2)
        | EBin (And, t1, t2) -> mk_or (mk_not t1) (mk_not t2)
        | _ -> t )
    | _ -> t
  in
  let rec apply_until_stable k t =
    let t' = Transform.apply_rule rule t in
    if ACES.equal t' t || k <= 0 then t' else apply_until_stable (k - 1) t'
  in
  apply_until_stable 100 t

(** All simplification rules. Does not take advantage of associativity/comutativity directly, the whole
    mechanism needs improvement.
*)
let simplify_easy (t : term) =
  let rule t =
    match t.texpr with
    | EIte (c, tt, tf) -> (
        match c.texpr with
        | EConst (CBool true) -> tt
        | EConst (CBool false) -> tf
        | _ -> (
            match (tt.texpr, tf.texpr) with
            | _ when ACES.(tt = tf) -> tt
            | EConst (CBool true), EConst (CBool false) -> c
            | EConst (CBool false), EConst (CBool true) -> mk_not c
            | _, _ -> t ) )
    | EBin (And, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | _ when ACES.(t1 = t2) -> t1
        | EConst (CBool true), _ -> t2
        | _, EConst (CBool true) -> t1
        | EConst (CBool false), _ -> mk_false
        | _, EConst (CBool false) -> mk_false
        | EUn (Not, t1), EUn (Not, t2) -> mk_not (mk_or t1 t2)
        | _, _ -> if ACES.(t1 = t2) then t1 else t )
    | EBin (Or, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EConst (CBool false), _ -> t2
        | _, EConst (CBool false) -> t1
        | EConst (CBool true), _ -> mk_true
        | _, EConst (CBool true) -> mk_true
        | (EBin (And, t1, t2), EUn (Not, t1') | EUn (Not, t1'), EBin (And, t1, t2))
          when ACES.(t1' = t1) ->
            mk_or (mk_not t1') t2
        | (EBin (And, t1, t2), EUn (Not, t1') | EUn (Not, t1'), EBin (And, t1, t2))
          when ACES.(t1' = t2) ->
            mk_or (mk_not t1') t1
        | EBin (Lt, t11, t12), EBin (Eq, t11', t12') ->
            if ACES.((t11 = t11' && t12 = t12') || (t11 = t12' && t12 = t12')) then
              mk_bin t11 Le t12
            else t
        | EBin (Gt, t11, t12), EBin (Eq, t11', t12') ->
            if ACES.((t11 = t11' && t12 = t12') || (t11 = t12' && t12 = t12')) then
              mk_bin t11 Ge t12
            else t
        | _, EUn (Not, t1') when ACES.(t1 = t1') -> mk_true
        | EUn (Not, t2'), _ when ACES.(t2 = t2') -> mk_true
        | _, _ -> if ACES.(t1 = t2) then t1 else t )
    | EBin (Max, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EBin (Plus, a, k), _ when ACES.(a = t2) && is_positive k -> mk_add a k
        | EBin (Plus, a, k), _ when ACES.(a = t2) && is_negative k -> a
        | _, EBin (Plus, e2, e3) when ACES.(t1 = e3) && is_positive e2 -> mk_add e2 e3
        | _, EBin (Plus, e2, e3) when ACES.(t1 = e3) && is_negative e2 -> t1
        | _, EBin (Minus, e2, e3) when ACES.(t1 = e2) && is_positive e3 -> t1
        | _, EBin (Minus, e2, e3) when ACES.(t1 = e2) && is_negative e3 -> mk_sub e2 e3
        | EBin (Minus, e2, e3), _ when ACES.(e2 = t2) && is_positive e3 -> t2
        | EBin (Minus, e2, e3), _ when ACES.(t2 = e2) && is_negative e3 -> mk_sub e2 e3
        | _ -> t )
    | EBin (Min, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EBin (Plus, a, k), _ when ACES.(a = t2) && is_positive k -> a
        | EBin (Plus, a, k), _ when ACES.(a = t2) && is_negative k -> mk_add a k
        | _, EBin (Plus, e2, e3) when ACES.(t1 = e3) && is_positive e2 -> t1
        | _, EBin (Plus, e2, e3) when ACES.(t1 = e3) && is_negative e2 -> mk_add e2 e3
        | _, EBin (Minus, e2, e3) when ACES.(t1 = e2) && is_positive e3 -> mk_sub e2 e3
        | _, EBin (Minus, e2, e3) when ACES.(t1 = e2) && is_negative e3 -> t1
        | EBin (Minus, e2, e3), _ when ACES.(e2 = t2) && is_positive e3 -> mk_sub e2 e3
        | EBin (Minus, e2, e3), _ when ACES.(t2 = e2) && is_negative e3 -> t2
        | _ -> t )
    | EBin (Mod, t1, { texpr = EConst (CInt 1); _ }) -> t1
    | EBin (op, e1, e2) when ACES.(e1 = e2) && is_idempotent op -> e1
    | EBin (Cons, empty_t, t1) -> (
        match empty_t.texpr with EConst CEmpty -> mk_list [ t1 ] | _ -> t )
    | EBin (BChoice (hd :: _), t1, t2) -> mk_bin t1 hd t2
    (* Const *)
    | EConst _ -> t
    (* Unary *)
    | EUn (Id, t1) -> t1
    | EUn (UChoice (hd :: _), t1) -> mk_un hd t1
    | EUn (Not, { texpr = EUn (Not, x); _ }) -> x
    | EUn (Not, { texpr = EConst (CBool b); _ }) -> if b then mk_false else mk_true
    | EBin (Eq, t1, t2) when ACES.(t1 = t2) -> mk_true
    | EBin (Eq, { texpr = EConst (CInt i1); _ }, { texpr = EConst (CInt i2); _ }) ->
        if i1 = i2 then mk_true else mk_false
    | EChoice (hd :: _) -> hd
    | _ -> t
  in
  let rec apply_until_stable k t =
    let t' = Transform.apply_rule rule t in
    if ACES.equal t' t || k <= 0 then t' else apply_until_stable (k - 1) t'
  in
  let t' = apply_until_stable 100 t in
  distrib_neg t'

let norm (t : term) =
  let rule t =
    match t.texpr with
    | EIte (a, b, c) ->
        if Set.length (Analyze.free_variables b) >= Set.length (Analyze.free_variables c) then t
        else mk_ite (mk_not a) c b
    | _ -> t
  in
  let rec apply_until_stable k t =
    let t' = Transform.apply_rule rule t in
    if ACES.equal t' t || k <= 0 then t' else apply_until_stable (k - 1) t'
  in
  let t' = apply_until_stable 20 t in
  distrib_neg t'

let simplify_full (t : term) =
  let rule t =
    match t.texpr with
    | EIte (c, tt, tf) -> (
        match c.texpr with
        | EConst (CBool true) -> tt
        | EConst (CBool false) -> tf
        | _ -> (
            match (tt.texpr, tf.texpr) with
            | _ when ACES.(tt = tf) -> tt
            | EConst (CBool true), EConst (CBool false) -> c
            | EConst (CBool false), _ -> mk_and (mk_not c) tf
            | _, EConst (CBool false) -> mk_and c tt
            | EConst (CBool true), _ -> mk_or c tf
            | _, EConst (CBool true) -> mk_or (mk_not c) tt
            | _, _ -> t ) )
    | EBin (And, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | _ when ACES.(t1 = t2) -> t1
        | EConst (CBool true), _ -> t2
        | _, EConst (CBool true) -> t1
        | EConst (CBool false), _ -> mk_false
        | _, EConst (CBool false) -> mk_false
        | EUn (Not, t1), EUn (Not, t2) -> mk_not (mk_or t1 t2)
        | EUn (Not, t1'), _ when ACES.(t1' = t2) -> mk_false
        | _, EUn (Not, t2') when ACES.(t2' = t1) -> mk_false
        | _, EBin (Or, t1', t2') when ACES.(t1 = t1' || t1 = t2') -> t1
        | EBin (Or, t1', t2'), _ when ACES.(t2 = t1' || t2 = t2') -> t2
        | _, _ -> if ACES.(t1 = t2) then t1 else t )
    | EBin (Or, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EConst (CBool false), _ -> t2
        | _, EConst (CBool false) -> t1
        | EConst (CBool true), _ -> mk_true
        | _, EConst (CBool true) -> mk_true
        | (EBin (And, t1, t2), EUn (Not, t1') | EUn (Not, t1'), EBin (And, t1, t2))
          when ACES.(t1' = t1) ->
            mk_or (mk_not t1') t2
        | (EBin (And, t1, t2), EUn (Not, t1') | EUn (Not, t1'), EBin (And, t1, t2))
          when ACES.(t1' = t2) ->
            mk_or (mk_not t1') t1
        | EBin (Lt, t11, t12), EBin (Eq, t11', t12') ->
            if ACES.((t11 = t11' && t12 = t12') || (t11 = t12' && t12 = t12')) then
              mk_bin t11 Le t12
            else t
        | EBin (Gt, t11, t12), EBin (Eq, t11', t12') ->
            if ACES.((t11 = t11' && t12 = t12') || (t11 = t12' && t12 = t12')) then
              mk_bin t11 Ge t12
            else t
        | _, EUn (Not, t1') when ACES.(t1 = t1') -> mk_true
        | EUn (Not, t2'), _ when ACES.(t2 = t2') -> mk_true
        | _, _ -> if ACES.(t1 = t2) then t1 else t )
    | EBin (Max, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EConst (CInt i1), EConst (CInt i2) -> mk_int (max i1 i2)
        | EBin (Plus, a, k), _ when ACES.(a = t2) && is_positive k -> mk_add a k
        | EBin (Plus, a, k), _ when ACES.(a = t2) && is_negative k -> a
        | _, EBin (Plus, e2, e3) when ACES.(t1 = e3) && is_positive e2 -> mk_add e2 e3
        | _, EBin (Plus, e2, e3) when ACES.(t1 = e3) && is_negative e2 -> t1
        | _, EBin (Minus, e2, e3) when ACES.(t1 = e2) && is_positive e3 -> t1
        | _, EBin (Minus, e2, e3) when ACES.(t1 = e2) && is_negative e3 -> mk_sub e2 e3
        | EBin (Minus, e2, e3), _ when ACES.(e2 = t2) && is_positive e3 -> t2
        | EBin (Minus, e2, e3), _ when ACES.(t2 = e2) && is_negative e3 -> mk_sub e2 e3
        | EBin (Max, e1, e2), _ when ACES.(t2 = e2 || t2 = e1) -> t1
        | _, EBin (Max, e1, e2) when ACES.(t1 = e2 || t1 = e1) -> t2
        | _ -> t )
    | EBin (Min, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EConst (CInt i1), EConst (CInt i2) -> mk_int (min i1 i2)
        | EBin (Plus, a, k), _ when ACES.(a = t2) && is_positive k -> a
        | EBin (Plus, a, k), _ when ACES.(a = t2) && is_negative k -> mk_add a k
        | _, EBin (Plus, e2, e3) when ACES.(t1 = e3) && is_positive e2 -> t1
        | _, EBin (Plus, e2, e3) when ACES.(t1 = e3) && is_negative e2 -> mk_add e2 e3
        | _, EBin (Minus, e2, e3) when ACES.(t1 = e2) && is_positive e3 -> mk_sub e2 e3
        | _, EBin (Minus, e2, e3) when ACES.(t1 = e2) && is_negative e3 -> t1
        | EBin (Minus, e2, e3), _ when ACES.(e2 = t2) && is_positive e3 -> mk_sub e2 e3
        | EBin (Minus, e2, e3), _ when ACES.(t2 = e2) && is_negative e3 -> t2
        | EBin (Min, e1, e2), _ when ACES.(t2 = e2 || t2 = e1) -> t1
        | _, EBin (Min, e1, e2) when ACES.(t1 = e2 || t1 = e1) -> t2
        | _ -> t )
    | EBin (Plus, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EConst (CInt i1), EConst (CInt i2) -> mk_int (i1 + i2)
        | _, EConst (CInt 0) -> t1
        | EConst (CInt 0), _ -> t2
        | _ -> t )
    | EBin (Minus, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EConst (CInt i1), EConst (CInt i2) -> mk_int (i1 - i2)
        | _, EConst (CInt 0) -> t1
        | EConst (CInt 0), _ -> mk_un Neg t2
        | _ -> t )
    | EBin (Times, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EConst (CInt i1), EConst (CInt i2) -> mk_int (i1 * i2)
        | _, EConst (CInt 1) -> t1
        | EConst (CInt 1), _ -> t2
        | _ -> t )
    | EBin (Div, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EConst (CInt i1), EConst (CInt i2) -> mk_int (i1 / i2)
        | _, EConst (CInt 1) -> t1
        | _ -> t )
    | EBin (Mod, t1, t2) -> (
        match (t1.texpr, t2.texpr) with
        | EConst (CInt i1), EConst (CInt i2) -> mk_int (i1 % i2)
        | _, EConst (CInt 1) -> t1
        | _ -> t )
    | EBin (op, e1, e2) when ACES.(e1 = e2) && is_idempotent op -> e1
    | EBin (Cons, empty_t, t1) -> (
        match empty_t.texpr with EConst CEmpty -> mk_list [ t1 ] | _ -> t )
    | EBin (BChoice (hd :: _), t1, t2) -> mk_bin t1 hd t2
    (* Const *)
    | EConst _ -> t
    (* Unary *)
    | EUn (Id, t1) -> t1
    | EUn (UChoice (hd :: _), t1) -> mk_un hd t1
    | EUn (Not, { texpr = EUn (Not, x); _ }) -> x
    | EUn (Not, { texpr = EConst (CBool b); _ }) -> if b then mk_false else mk_true
    | EUn (Not, t1) -> (
        match t1.texpr with
        | EBin (Lt, t1', t2') -> mk_bin t1' Ge t2'
        | EBin (Gt, t1', t2') -> mk_bin t1' Le t2'
        | EBin (Le, t1', t2') -> mk_bin t1' Gt t2'
        | EBin (Ge, t1', t2') -> mk_bin t1' Lt t2'
        | _ -> t )
    | EUn (Neg, { texpr = EConst (CInt 0); _ }) -> mk_int 0
    | EBin (Eq, t1, t2) when ACES.(t1 = t2) -> mk_true
    | EBin (Eq, { texpr = EConst (CInt i1); _ }, { texpr = EConst (CInt i2); _ }) ->
        if i1 = i2 then mk_true else mk_false
    | EChoice (hd :: _) -> hd
    | _ -> t
  in
  let rec apply_until_stable k t =
    let t' = Transform.apply_rule rule t in
    if ACES.equal t' t || k <= 0 then t' else apply_until_stable (k - 1) t'
  in
  apply_until_stable 100 t

let factorize (to_factorize : term list) (term : term) : term =
  let reconstr_app op l =
    match mk_ac_app op l with
    | Some app -> app
    | None -> (
        match mk_a_app op l with
        | Some app -> app
        | None ->
            failhere Caml.__FILE__ "reconstr_app" "Something went wrong went rebuilding ac app." )
  in
  let factorize_args opmax args =
    let empty_bmap = Map.empty (module Binop) in
    let fold_op (_map, _list) _t =
      match _t.texpr with
      | EApp (vt, args') -> (
          match vt.texpr with
          | EVar (Var opplus) -> (
              match get_op opplus with
              | Some opplus when distributes opplus opmax ->
                  (bmap_terml_add opplus args' _map, _list)
              | _ -> (_map, _list @ [ _t ]) )
          | _ -> (_map, _list @ [ _t ]) )
      | EBin (opplus, e1, e2) when distributes opplus opmax ->
          (bmap_terml_add opplus [ e1; e2 ] _map, _list)
      | _ -> (_map, _list @ [ _t ])
    in
    let args_of_binops, rest = List.fold_left args ~f:fold_op ~init:(empty_bmap, []) in
    let init_factor_counts = List.map ~f:(fun x -> (0, x)) to_factorize in
    let cnt_factors tl =
      List.fold_left
        ~f:(fun _l x -> List.map ~f:(fun (c, y) -> if ACES.(x = y) then (c + 1, y) else (c, y)) _l)
        ~init:init_factor_counts tl
    in
    let bfold ~key ~data:_args_lists _top_args =
      let cnts = List.map ~f:(fun argl -> (cnt_factors argl, argl)) _args_lists in
      let _, best_factor =
        let _f _fcnt (_cnts, _) =
          match List.map2 ~f:(fun (c1, x1) (c2, _) -> (c1 + c2, x1)) _fcnt _cnts with
          | List.Or_unequal_lengths.Ok l -> l
          | _ -> failhere Caml.__FILE__ "factorize" "List unequal lengths."
        in
        let max_factor_o =
          ListTools.mmax (fun (c, _) -> c) (List.fold_left ~f:_f ~init:init_factor_counts cnts)
        in
        match max_factor_o with
        | Some (a, b) -> (a, b)
        | None ->
            Log.warning_msg
              Fmt.(str "Could not find best factor: %a" (list ~sep:comma pp_term) _top_args);
            raise_s (Sexp.Atom "Could not find best factor.")
      in
      let operands, nonfactors =
        let _f (_op, _nonf) _args =
          if List.mem ~equal:ACES.equal _args best_factor && List.length _args > 1 then
            (_op @ [ reconstr_app key (ListTools.remove_elt best_factor _args) ], _nonf)
          else (_op, _nonf @ [ reconstr_app key _args ])
        in
        List.fold_left ~f:_f ~init:([], []) _args_lists
      in
      let factorized_expr =
        match operands with
        | [] | [ _ ] -> List.map ~f:(reconstr_app key) _args_lists
        | _ -> [ reconstr_app key [ best_factor; reconstr_app opmax operands ] ]
      in
      if List.length nonfactors > 0 then factorized_expr @ nonfactors @ _top_args
      else factorized_expr @ _top_args
    in
    Map.fold ~init:rest ~f:bfold args_of_binops
  in
  let rec aux t =
    {
      t with
      texpr =
        ( match t.texpr with
        | EApp (opv, args) -> (
            match get_op_t opv with
            | Some op -> (
                try EApp (opv, factorize_args op (List.map ~f:aux args))
                with _ -> EApp (opv, List.map ~f:aux args) )
            | None -> EApp (opv, List.map ~f:aux args) )
        | EBin (op, e1, e2) -> EBin (op, aux e1, aux e2)
        | EUn (op, e1) -> EUn (op, aux e1)
        | ETuple el -> ETuple (List.map ~f:aux el)
        | EList el -> EList (List.map ~f:aux el)
        | EIte (c, e1, e2) -> EIte (aux c, aux e1, aux e2)
        | ELet (v, e1, e2) -> ELet (v, aux e1, aux e2)
        | ELambda (args, body) -> ELambda (args, aux body)
        | EFoldL (f, e0, el) -> EFoldL (aux f, aux e0, aux el)
        | EFoldR (f, e0, el) -> EFoldR (aux f, aux e0, aux el)
        | _ -> t.texpr );
    }
  in
  aux (to_ac term)

let of_conj (t : term) : term list =
  let flat_t = to_ac t in
  match flat_t.texpr with
  | EApp (vt, args) -> (
      match vt.texpr with
      | EVar (Var vop) -> ( match get_op vop with Some And -> args | _ -> [ t ] )
      | _ -> [ t ] )
  | _ -> [ t ]

let add_computed_attributes (t : term) ~prev:(computed_prev : term Array.t option)
    ~cur:(computed_cur : term Array.t) : term =
  let _t =
    match computed_prev with
    | Some computed_prev -> (
        fun _ t ->
          match Array.findi ~f:(fun _ ct -> ACES.(t = ct)) computed_cur with
          | Some (i, _) -> Some (add_attr (Computed (i, 0)) t)
          | None -> (
              match Array.findi ~f:(fun _ ct -> ACES.(t = ct)) computed_prev with
              | Some (i, _) -> Some (add_attr (Computed (i, -1)) t)
              | None -> None ) )
    | None -> (
        fun _ t ->
          match Array.findi ~f:(fun _ ct -> ACES.(t = ct)) computed_cur with
          | Some (i, _) -> Some (add_attr (Computed (i, 0)) t)
          | None -> None )
  in
  Transform.transform _t t

let is_computed : term -> bool =
  has_attr_kind (fun x -> match x with Computed _ -> true | _ -> false)
