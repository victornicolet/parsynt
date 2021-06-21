(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
*)

open Beta
open Fn
open Utils
open Utils.ListTools

let rec hash_str s =
  if String.length s > 0 then
    int_of_char (String.get s 0) + (hash_str (String.sub s 1 (String.length s - 1)) * 10)
  else 0

module SH = Hashtbl.Make (struct
  type t = string

  let equal s s' = s = s'

  let hash s = hash_str s
end)

(* Utils *)
let update_assocmap (op : symb_binop) (elt : 'a) (amap : 'a list BinopMap.t) =
  if BinopMap.mem op amap then
    let p = BinopMap.find op amap in
    BinopMap.add op (elt :: p) amap
  else BinopMap.add op [ elt ] amap

let split_input_state (ctx : context) (el : fnExpr list) : fnExpr list * fnExpr list =
  List.partition
    (fun e -> match e with FnVar a -> VarSet.mem (var_of_fnvar a) ctx.state_vars | _ -> false)
    el

(* Other expression properties *)
let is_constant expr =
  rec_expr2
    {
      join = (fun a b -> a && b);
      init = true;
      case = (fun _ -> false);
      on_case = (fun _ _ -> true);
      on_const = (fun _ -> true);
      on_var = (fun _ -> false);
    }
    expr

type optyp =
  | BinInt of (int -> int -> int)
  | UnInt of (int -> int)
  | BinBool of (bool -> bool -> bool)
  | UnBool of (bool -> bool)
  | Comp of (int -> int -> bool)
  | NotInterpreted

let rec concrete_eval (expr : fnExpr) : fnExpr =
  assert (is_constant expr);
  match expr with
  | FnBinop (op, e1, e2) -> (
      let concr_op =
        match op with
        | Plus -> BinInt ( + )
        | Minus -> BinInt ( - )
        | Times -> BinInt ( * )
        | Max -> BinInt max
        | Min -> BinInt min
        | Div -> BinInt ( / )
        | And -> BinBool ( && )
        | Or -> BinBool ( || )
        | Lt -> Comp ( < )
        | Gt -> Comp ( > )
        | Le -> Comp ( <= )
        | Ge -> Comp ( >= )
        | Eq -> Comp ( = )
        | Neq -> Comp ( != )
        | _ -> NotInterpreted
      in
      match (concr_op, concrete_eval e1, concrete_eval e2) with
      | BinInt o, FnConst (CInt i1), FnConst (CInt i2) -> FnConst (CInt (o i1 i2))
      | BinBool b, FnConst (CBool b1), FnConst (CBool b2) -> FnConst (CBool (b b1 b2))
      | Comp c, FnConst (CInt i1), FnConst (CInt i2) -> FnConst (CBool (c i1 i2))
      | _ -> expr)
  | FnUnop (op, e1) -> (
      let concr_op =
        match op with
        | Neg -> UnInt (fun i -> -i)
        | Add1 -> UnInt (fun i -> i + 1)
        | Sub1 -> UnInt (fun i -> i - 1)
        | Not -> UnBool not
        | Abs -> UnInt abs
        | _ -> NotInterpreted
      in
      match (concr_op, concrete_eval e1) with
      | UnInt o, FnConst (CInt i1) -> FnConst (CInt (o i1))
      | UnBool b, FnConst (CBool b1) -> FnConst (CBool (b b1))
      | _ -> expr)
  | FnConst c -> ( match c with CInt64 i64 -> FnConst (CInt (Int64.to_int i64)) | _ -> expr)
  | FnCond (c, e1, e2) -> (
      match concrete_eval c with
      | FnConst (CBool true) -> concrete_eval e1
      | FnConst (CBool false) -> concrete_eval e2
      | _ -> expr)
  | _ -> expr

let conv_ints = function CInt64 i64 -> CInt (Int64.to_int i64) | c -> c

let peval (expr : fnExpr) : fnExpr =
  transform_expr2
    {
      case = is_constant;
      on_case = (fun _ e -> concrete_eval e);
      on_var = identity;
      on_const = conv_ints;
    }
    expr

(* List different types of operators:
    - comparison operators
    - associative operators
    - commutative operators

    And properties:
    - left and right distributivity.
*)

let comparison_operators : symb_binop list = [ Gt; Ge; Lt; Le ]

let associative_operators = [ And; Or; Plus; Max; Min; Times ]

let commutative_operators = [ And; Or; Plus; Max; Min; Times; Eq; Neq ]

let is_associative op = List.mem op associative_operators

let is_commutative op = List.mem op commutative_operators

let is_right_distributive op1 op2 =
  (* (a op1 b) op2 c = (a op2 c) op1 (b op2 c) *)
  match (op1, op2) with Or, And | Min, Plus | Max, Plus | Plus, Times -> true | _, _ -> false

let is_left_distributive op1 op2 =
  (*  a op2 (b op1 c) = (a op1 b) op2 (a op1 c) *)
  match (op1, op2) with Plus, Times | Max, Plus | Min, Plus | Or, And -> true | _, _ -> false

(* Operator -> variable *)
let int_function = Function (List (Integer, None), Integer)

let bool_function = Function (List (Boolean, None), Boolean)

let named_AC_ops = SH.create 10

(* Initialize map *)

;;
SH.add named_AC_ops "plus" (mkFnVar "plus" int_function);
SH.add named_AC_ops "times" (mkFnVar "times" int_function);
SH.add named_AC_ops "max" (mkFnVar "max" int_function);
SH.add named_AC_ops "min" (mkFnVar "min" int_function);
SH.add named_AC_ops "and" (mkFnVar "and" bool_function);
SH.add named_AC_ops "or" (mkFnVar "or" bool_function)

let get_AC_op op =
  let fsh = SH.find named_AC_ops in
  match op with
  | Plus -> fsh "plus"
  | Times -> fsh "times"
  | Max -> fsh "max"
  | Min -> fsh "min"
  | And -> fsh "and"
  | Or -> fsh "or"
  | _ -> raise Not_found

let op_from_name name : symb_binop option =
  match name with
  | "plus" -> Some Plus
  | "times" -> Some Times
  | "and" -> Some And
  | "or" -> Some Or
  | "min" -> Some Min
  | "max" -> Some Max
  | _ -> None

(* Identity rules *)
let operators_with_identities : symb_binop list = [ Minus; Plus; Times; Div ]

let apply_right_identity _ _ e = e

let apply_left_identity _ _ e = e

(** Flatten trees with a AC spine. Expressions are encoded via function
    applications : the function is named after the operator in the stringhash
    above.
*)
let rec flatten_AC (expr : fnExpr) =
  let rec flatten cur_op expr =
    match expr with
    | FnBinop (op, e1, e2) when op = cur_op -> flatten cur_op e1 @ flatten cur_op e2
    | e -> [ flatten_AC e ]
  in
  let filter_exprs e =
    match e with
    | FnBinop (op, _, _) when is_associative op && is_commutative op -> true
    | _ -> false
  in
  let flatten_expr rfunc e =
    match e with
    | FnBinop (op, e1, e2) when is_associative op && is_commutative op ->
        let operands = flatten op e1 @ flatten op e2 in
        assert (List.length operands > 0);
        let func_vi = get_AC_op op in
        FnApp (Integer, Some func_vi, operands)
    | _ -> rfunc e
  in
  transform_expr filter_exprs flatten_expr identity identity expr

let rec normalize_AC (expr : fnExpr) =
  let remove f all el =
    List.map f (List.filter (fun e -> not (List.exists (fun r -> e @= r) all)) el)
  in
  let case e = match e with FnApp (_, Some _, _) -> true | _ -> false in
  let on_case f e =
    match e with
    | FnApp (vt, Some opf, args) -> (
        let true_op = op_from_name opf.vname in
        match true_op with
        | Some op -> (
            match op with
            | Plus -> FnApp (vt, Some opf, remove f [ FnConst (CInt 0); FnConst (CInt64 0L) ] args)
            | Times -> FnApp (vt, Some opf, remove f [ FnConst (CInt 1); FnConst (CInt64 1L) ] args)
            | And -> FnApp (vt, Some opf, remove f [ FnConst (CBool true) ] args)
            | Or -> FnApp (vt, Some opf, remove f [ FnConst (CBool false) ] args)
            | _ -> FnApp (vt, Some opf, List.map f args))
        | None -> FnApp (vt, Some opf, List.map f args))
    | _ -> e
  in
  transform_expr2 { case; on_case; on_var = identity; on_const = identity } expr

(** Equality under associativity and commutativity. Can be defined
    as structural equality of expressions trees with reordering in flat
    terms *)
and ( @= ) e1 e2 =
  let rec aux_eq e1 e2 =
    match (e1, e2) with
    | FnBinop (op1, e11, e12), FnBinop (op2, e21, e22) ->
        let strict_equal = op1 = op2 && aux_eq e11 e21 && aux_eq e12 e22 in
        let comm_eq = op1 = op2 && is_commutative op1 && aux_eq e11 e22 && aux_eq e12 e21 in
        strict_equal || comm_eq
    | FnUnop (op1, e11), FnUnop (op2, e21) -> op1 = op2 && aux_eq e11 e21
    | FnApp (_, Some v1, el1), FnApp (_, Some v2, el2) ->
        if v1 = v2 then
          try
            let op = op_from_name v1.vname in
            match op with
            | Some op ->
                is_commutative op
                && List.length el1 = List.length el2
                && List.for_all (fun elt1 -> List.exists (fun elt2 -> aux_eq elt1 elt2) el2) el1
                && List.for_all (fun elt2 -> List.exists (fun elt1 -> aux_eq elt1 elt2) el1) el2
            | None -> el1 = el2
          with Not_found -> el1 = el2
        else false
    | FnCond (c1, e11, e12), FnCond (c2, e21, e22) ->
        aux_eq c1 c2 && aux_eq e11 e21 && aux_eq e12 e22
    | FnVector el, FnVector el' -> List.for_all2 aux_eq el el'
    | _, _ -> e1 = e2
  in
  let t = flatten_AC --> normalize_AC --> peval in
  aux_eq (t e1) (t e2)

(* Set of expressions, equipped with the associative and commutative
   equality.
 *)
module ACES = Set.Make (struct
  type t = fnExpr

  let compare x y = if x @= y then 0 else 1
end)

let es_to_aces s = ACES.of_list (ES.elements s)

let update_assoc_ace al (op, a) b =
  match
    List.fold_left
      (fun (found, nl) ((op', a'), b') ->
        if (a' @= a) && op' = op then (true, ((op, a), b :: b') :: nl)
        else (found, ((op', a'), b') :: nl))
      (false, []) al
  with
  | true, nl -> nl
  | false, nl -> ((op, a), [ b ]) :: nl

(* Expression cost: the number of occurrences of
   an expression and the maximal depth of an expression. *)
type ecost = { occurrences : int; max_depth : int; indexation : int }

let expression_cost ctx e =
  let idx =
    match e with
    | FnVar (FnArray (_, FnConst (CInt i))) -> i
    | FnVar (FnArray (_, FnConst (CInt64 i))) -> Int64.to_int i
    | FnVar (FnArray (_, FnBinop (Plus, _, FnConst (CInt i))))
    | FnVar (FnArray (_, FnBinop (Plus, FnConst (CInt i), _))) ->
        i
    | FnVar (FnArray (_, FnBinop (Plus, _, FnConst (CInt64 i))))
    | FnVar (FnArray (_, FnBinop (Plus, FnConst (CInt64 i), _))) ->
        Int64.to_int i
    | _ -> 0
  in
  let ctx_costlies = es_to_aces ctx.costly_exprs in
  let case0 = { occurrences = 0; max_depth = 0; indexation = idx } in
  let case1 = { occurrences = 1; max_depth = 1; indexation = idx } in
  let join_c c1 c2 =
    let mdepth =
      let mx = max c1.max_depth c2.max_depth in
      if mx > 0 then mx + 1 else 0
    in
    { occurrences = c1.occurrences + c2.occurrences; max_depth = mdepth; indexation = idx }
  in
  let special_case e = ACES.mem e ctx_costlies in
  let handle_spec _ _ = case1 in
  let case_var v =
    let vi_o = vi_of v in
    match vi_o with Some vi -> if VarSet.mem vi ctx.state_vars then case1 else case0 | _ -> case0
  in
  let case_const _ = case0 in
  rec_expr join_c case0 special_case handle_spec case_const case_var e

let compare_ecost ec1 ec2 =
  let ccost (d1, o1, i1) (d2, o2, i2) =
    if d1 = d2 then
      if o1 = o2 then (* Order indexes in increasing order. *)
        compare i2 i1 else compare o1 o2
    else compare d1 d2
  in
  ccost
    (ec1.max_depth, ec1.occurrences, ec1.indexation)
    (ec2.max_depth, ec2.occurrences, ec2.indexation)

let compare_cost ctx e1 e2 = compare_ecost (expression_cost ctx e1) (expression_cost ctx e2)

(** Compute the 'cost' of an expression with respect to a set of other
    c-expressions : the cost is the pair of the maximum depth of a
    c-expression in the expressions and the number of c-expressions in
    the expressions.
    @param stv the set of state variables.
    @param expr the expression of which we need to compute the cost.
    @return a pair of ints, the first element is the maximum depth of
    c-expression in the expression abstract syntax tree and the second element
    is the number of occurrences of c-expressions.
*)
let rec depth_cost ctx expr =
  let cost = expression_cost ctx expr in
  (cost.max_depth, cost.occurrences)

and depth_c_func ctx func =
  match func with
  | FnLetIn (velist, l') ->
      let dl', cl' = depth_c_func ctx l' in
      let max_de, sum_c =
        List.fold_left
          (fun (mde, sec) (de, ec) -> (max mde de, sec + ec))
          (0, 0)
          (List.map (fun (_, e) -> depth_cost ctx e) velist)
      in
      (max max_de (if dl' > 0 then dl' + 1 else 0), sum_c + cl')
  | FnRecord (vs, emap) ->
      List.fold_left
        (fun (mde, sec) (de, ec) -> (max mde de, sec + ec))
        (0, 0)
        (List.map (fun (_, e) -> depth_cost ctx e) (unwrap_state vs emap))
  | _ -> (0, 0)

let cost ctx expr = depth_cost ctx expr

(* AC rules *)

let e_of_ac_op e = match e with FnApp (_, Some f, _) -> SH.mem named_AC_ops f.vname | _ -> false

let op_of_ac_e e = match e with FnApp (_, Some f, _) -> op_from_name f.vname | _ -> None

let args_of_ac_e e = match e with FnApp (_, _, el) when e_of_ac_op e -> Some el | _ -> None

(* Rebuild an expression from its flattened expression. *)
let rebuild_tree_AC ctx =
  let rebuild_flat_expr rfunc e =
    match e with
    | FnApp (_, Some f, el) -> (
        match op_from_name f.vname with
        | Some op -> (
            let el' = List.map rfunc el in
            let el_ord = List.sort (compare_cost ctx) el' in
            match el_ord with
            | hd :: tl -> List.fold_left (fun tree e -> FnBinop (op, e, tree)) hd tl
            | [] ->
                failhere __FILE__ "rebuild_tree_AC" "Unexpected length for list in AC conversion.")
        | None -> failwith "Rebuild_flat_expr : Unexpected case.")
    | _ -> failwith "Rebuild_flat_expr : Unexpected case."
  in
  transform_expr e_of_ac_op rebuild_flat_expr identity identity

(** Special rules, tranformations. *)

(**
   Work in progress: multidimensional data structure support.
   Add some facotrization rules that take multiple elements
   at a time.
*)
let costly_arrays ctx =
  ListTools.mapoption
    (fun e -> match e with FnVar (FnArray (FnVariable a, _)) -> Some a | _ -> None)
    (ES.elements ctx.costly_exprs)

let costly_vars ctx =
  ListTools.mapoption
    (fun e -> match e with FnVar (FnVariable a) -> Some a | _ -> None)
    (ES.elements ctx.costly_exprs)

type expression_flavour = Normal | State | Input | Const | NonNormal

let locality_rule ctx e =
  let cvs = VarSet.of_list (costly_vars ctx) in
  let ctas = VarSet.of_list (costly_arrays ctx) in
  rec_expr2
    {
      join =
        (fun f1 f2 ->
          match (f1, f2) with
          | e1, e2 when e1 = e2 -> e1
          | State, Input -> Normal
          | Input, State -> Normal
          | Normal, Normal -> Normal
          | Const, e1 | e1, Const -> e1
          | _, _ -> NonNormal);
      init = Normal;
      case = (fun _ -> false);
      on_case = (fun _ _ -> Normal);
      on_var =
        (fun v ->
          match v with
          | FnArray (FnVariable c, _) -> if VarSet.mem c ctas then State else Input
          | FnVariable v -> if VarSet.mem v cvs then State else Input
          | _ -> Input);
      on_const = (fun _ -> Const);
    }
    e

let is_normal = function NonNormal -> false | _ -> true

let collect_normal_subexpressions ctx =
  let add_guard c (cl, e) = (c :: cl, e) in
  let not c = FnUnop (Not, c) in
  rec_expr2
    {
      join = (fun x y -> x @ y);
      init = [];
      case = (fun e -> match e with FnBinop _ | FnUnop _ | FnCond _ -> true | _ -> false);
      on_case =
        (fun f e ->
          if is_normal (locality_rule ctx e) then [ ([], e) ]
          else
            match e with
            | FnBinop (_, e1, e2) -> f e1 @ f e2
            | FnUnop (_, e1) -> f e1
            | FnCond (c, e1, e2) ->
                List.map (add_guard c) (f e1) @ List.map (add_guard (not c)) (f e2)
            | _ -> failhere __FILE__ "collect" "x");
      on_var = (fun v -> [ ([], FnVar v) ]);
      on_const = (fun c -> [ ([], FnConst c) ]);
    }

(*
Factorize by finding common factors larger than a single expression.
 *)
let __factorize_multi__ ctx top_op el =
  let el = List.map (rebuild_tree_AC ctx) el in
  let el = List.map flatten_AC el in
  let ac_costlies = ACES.of_list (ES.elements ctx.costly_exprs) in
  let el_hasop, el_noop =
    List.partition
      (fun e ->
        match op_of_ac_e e with Some op -> is_right_distributive top_op op | None -> false)
      el
  in
  (* Transforms the list into a binary expression containing
     on one side the state variables, the other side other variables.
  *)
  let split_e =
    List.map
      (fun e ->
        match e with
        | FnApp (t, f, args) -> (
            let args1, args2 = List.partition (fun e -> ACES.mem e ac_costlies) args in
            let op = check_option (op_of_ac_e e) in
            match (List.length args1, List.length args2) with
            (* Initial list was empty? *)
            | 0, 0 -> e
            (* No 'costly' expression in the arguments. *)
            | 0, _ -> e
            (* All arguments are 'costly' *)
            | _, 0 -> e
            (* Costly part needs to be separated from inputs.
               Create a binary expression, with the first operand always
               being the operand containing the costly expressions.
            *)
            | _, _ -> FnBinop (op, FnApp (t, f, args1), FnApp (t, f, args2)))
        | _ -> e)
      el_hasop
  in
  let new_factorized_expr =
    let factor_assoc_list, rest =
      List.fold_left
        (fun (alist, rst) e ->
          match e with
          | FnBinop (op, ecostly, echeap) -> (update_assoc_ace alist (op, ecostly) echeap, rst)
          | _ -> (alist, e :: rst))
        ([], []) split_e
    in
    let factorized =
      List.map
        (fun ((op, a), bl) ->
          if List.length bl > 1 then
            FnBinop (op, a, FnApp (type_of (bl >> 0), Some (get_AC_op top_op), bl))
          else FnBinop (op, a, bl >> 0))
        factor_assoc_list
    in
    factorized @ rest
  in
  new_factorized_expr @ el_noop

let factorize_multi_toplevel ctx e =
  (* Transform apps where we can recognize the top operator. *)
  let e' = flatten_AC e in
  let eres =
    match e' with
    | FnApp (t, Some op, el) -> (
        match op_from_name op.vname with
        | Some op' -> FnApp (t, Some op, __factorize_multi__ ctx op' el)
        | None -> e')
    | _ -> e'
  in
  let e'' = rebuild_tree_AC ctx eres in
  e''

let find_max_state_factors (ctx : context) (t : fn_type) (top_op : fnV) (op : fnV)
    (ell : fnExpr list list) : fnExpr list =
  let separated_expr =
    (List.fold_left (fun assoc_list (h, l) ->
         try
           let assoc = List.assoc h assoc_list in
           let assoc_list' = List.remove_assoc h assoc_list in
           (h, l :: assoc) :: assoc_list'
         with Not_found -> (h, [ l ]) :: assoc_list))
      []
      (List.map
         (List.partition (fun expr ->
              let ec = expression_cost ctx expr in
              ec.occurrences > 0))
         ell)
  in
  List.map
    (fun (h, l) ->
      match (h, l) with
      | [], _ -> FnApp (t, Some top_op, List.map (fun args -> FnApp (t, Some op, args)) l)
      | _, [] -> FnApp (t, Some op, h)
      | _, _ ->
          FnBinop
            ( check_option (op_from_name op.vname),
              FnApp (t, Some op, h),
              FnApp (t, Some top_op, List.map (fun args -> FnApp (t, Some op, args)) l) ))
    separated_expr

(** Inverse distributivity / factorization.
    This step rebuilds expression trees, but has to flatten the expressions
    it returns *)
let extract_operand_lists el =
  List.fold_left
    (fun (l1, l2) e ->
      match e with FnBinop (_, e1, e2) -> (l1 @ [ e1 ], l2 @ [ e2 ]) | _ -> (l1, l2))
    ([], []) el

let __factorize_special_cases__ ctx top_op el =
  match top_op with
  | Min -> (
      let factorizable, _ =
        List.partition
          (fun e ->
            let e' = rebuild_tree_AC ctx e in
            match e' with FnBinop (Plus, _, _) -> true | _ -> false)
          el
      in
      try
        let el_sep =
          List.map
            (fun e ->
              match e with
              | FnApp (t, o, args) ->
                  let a, b = List.partition (fun e -> ES.mem e ctx.costly_exprs) args in
                  (FnApp (t, o, a), FnApp (t, o, b))
              | _ -> failwith "K")
            factorizable
        in
        match el_sep with
        | [] -> None
        | (state, _) :: _ ->
            if List.for_all (fun (s, _) -> s = state) el_sep then
              Some
                (FnApp
                   ( Integer,
                     Some (get_AC_op Plus),
                     [ FnApp (Integer, Some (get_AC_op Min), ListTools.lsnd el_sep); state ] ))
            else None
      with _ -> None)
  | _ -> None

let __factorize__ ctx top_op el =
  let el = List.map (rebuild_tree_AC ctx) el in
  let el_binops, el_no_binops =
    List.partition (function FnVar _ -> true | FnBinop (_, _, _) -> true | _ -> false) el
  in
  let rec do_binop op e1 e2 hd tl =
    let ce1 = cost ctx e1 in
    let ce2 = cost ctx e2 in

    if is_left_distributive top_op op && ce1 > ce2 then
      (* Look for similar expressions in the list *)
      let sim_exprs, rtl =
        List.partition
          (fun e ->
            match e with
            | FnBinop (op', e1', _) when op' = op && (e1' @= e1) -> true
            (* | FnBinop (op', ee, e1') when op' = op && e1' @= e1 && is_commutative op' ->
             *   true *)
            | _ -> false)
          tl
      in

      let _, sim_exprs_snd = extract_operand_lists sim_exprs in
      let new_exprs =
        FnBinop (op, e1, FnApp (type_of e2, Some (get_AC_op top_op), e2 :: sim_exprs_snd))
      in
      new_exprs :: regroup rtl
    else if is_right_distributive top_op op && ce2 < ce1 then
      let sim_exprs, rtl =
        List.partition
          (fun e ->
            match e with FnBinop (op', _, e2') when op' = op && (e2' @= e2) -> true | _ -> false)
          tl
      in
      (* Extract the list of the second operands of the list of
         binary operators *)
      let sim_exprs_fst, _ = extract_operand_lists sim_exprs in
      (* Build the new expression by lifting e2 on top at the
         right of the operator *)
      let new_exprs =
        FnBinop (op, FnApp (type_of e1, Some (get_AC_op top_op), e1 :: sim_exprs_fst), e2)
      in
      new_exprs :: regroup rtl
    else hd :: regroup tl
  (* Regroup expressions lists by common factors.
  *)
  and regroup el =
    match el with
    | hd :: tl -> (
        match hd with FnBinop (op, e1, e2) -> do_binop op e1 e2 hd tl | _ -> hd :: regroup tl)
    | [] -> []
  in
  let applied_different_right_identities =
    List.map
      (fun op ->
        List.map
          (fun e -> match e with FnVar _ -> apply_right_identity op (type_of e) e | _ -> e)
          el_binops)
      operators_with_identities
  in
  let applied_different_left_identities =
    List.map
      (fun op ->
        List.map
          (fun e -> match e with FnVar _ -> apply_left_identity op (type_of e) e | _ -> e)
          el_binops)
      operators_with_identities
  in
  let different_factorizations =
    List.map regroup
      (applied_different_left_identities @ applied_different_right_identities @ [ el_binops ])
  in
  let best_factorization =
    Option.value ~default:[] (ListTools.lmin List.length different_factorizations)
  in
  match __factorize_special_cases__ ctx top_op el with
  | Some e -> [ e ]
  | None -> List.map flatten_AC (best_factorization @ el_no_binops)

let __factorize_flat__ (ctx : context) (top : symb_binop) (el : fnExpr list) : fnExpr list =
  let bop_map, rest =
    List.fold_left
      (fun (m, r) e ->
        match e with
        | FnApp (t, Some opvar, args) -> (
            match op_from_name opvar.vname with
            | Some binop ->
                if is_left_distributive top binop then
                  let state, inputs = split_input_state ctx args in
                  let stateset = ACES.of_list state in
                  let inputset = ACES.of_list inputs in
                  (update_assocmap binop (t, stateset, inputset) m, r)
                else (m, e :: r)
            | None -> (m, e :: r))
        | _ -> (m, e :: r))
      (BinopMap.empty, []) el
  in
  let fact_map =
    let factor_or_flat op sli =
      let opvar = get_AC_op op in
      match sli with
      | [ (t, a, b) ] ->
          let al, bl = (ACES.elements a, ACES.elements b) in
          [ FnApp (t, Some opvar, al @ bl) ]
      | (t, a, _) :: _ ->
          let same_a, diff_a = List.partition (fun (_, a', _) -> a = a') sli in
          if List.length diff_a > 0 then raise Not_found
          else
            let factorized_expr =
              let bs =
                List.map
                  (fun targs ->
                    if ACES.cardinal targs < 1 then raise Not_found
                    else FnApp (t, Some opvar, ACES.elements targs))
                  (ListTools.lthird same_a)
              in
              let eb = [ FnApp (t, Some (get_AC_op top), bs) ] in
              let as' = ACES.elements a in
              [ FnApp (t, Some opvar, eb @ as') ]
            in
            factorized_expr
      | _ -> failwith "Empty list of operands should not have been added to map."
    in
    BinopMap.mapi factor_or_flat bop_map
  in
  let fact_elts = List.flatten (ListTools.lsnd (BinopMap.bindings fact_map)) in
  fact_elts @ rest

let factorize (ctx : context) : fnExpr -> fnExpr =
  (* Transform apps where we can recognize the top operator. *)
  let case e =
    match e with FnApp (_, Some opvar, _) -> is_some (op_from_name opvar.vname) | _ -> false
  in
  let fact rfunc e =
    match e with
    | FnApp (t, Some opvar, el) -> (
        let op_ = op_from_name opvar.vname in
        match op_ with
        | Some op ->
            (* let fact_el = __factorize__ ctx op (List.map rfunc el) in *)
            let fact_el =
              try __factorize_flat__ ctx op (List.map rfunc el)
              with Not_found -> __factorize__ ctx op (List.map rfunc el)
            in
            FnApp (t, Some opvar, fact_el)
        | None -> failhere __FILE__ "factorize_all" "bad case")
    | _ -> failhere __FILE__ "factorize_all" "bad case"
  in
  transform_expr case fact identity identity

(** Transform all comparisons : Lt -> Gt Le -> Ge *)
let transform_all_comparisons expr =
  let case e =
    match e with
    | FnBinop (cop, _, _) -> ( match cop with Lt | Le -> true | _ -> false)
    | _ -> false
  in
  let transformer rfunc e =
    match e with
    | FnBinop (cop, e1, e2) -> (
        match cop with
        | Lt -> FnBinop (Gt, rfunc e2, rfunc e1)
        | Le -> FnBinop (Ge, rfunc e2, rfunc e1)
        | _ -> failwith "Not a special recursive case")
    | _ -> failwith "Not a special recursive case"
  in
  transform_expr case transformer identity identity expr

let __transform_conj_comps__ top_op el =
  let with_comparison, rest =
    List.partition
      (fun e -> match e with FnBinop (op, _, _) -> List.mem op comparison_operators | _ -> false)
      el
  in
  (* Build max or min from conjunctions of comparisons.
     Rules:
     + a > b and c > b <=> min(a,c) > b.
     + a > b or c > b <=> max(a,c) > b.
  *)
  let build_comp_conj (is_left_operand : bool) (top_op : symb_binop) (op : symb_binop) common_expr
      exprs =
    if is_left_operand then
      let _, right_op_list = Base.List.unzip exprs in
      match (top_op, op) with
      | Or, Lt | Or, Le | And, Gt | And, Ge ->
          FnBinop (op, common_expr, FnApp (type_of common_expr, Some (get_AC_op Max), right_op_list))
      | And, Lt | And, Le | Or, Gt | Or, Ge ->
          FnBinop (op, common_expr, FnApp (type_of common_expr, Some (get_AC_op Min), right_op_list))
      | _, _ -> failhere __FILE__ "build_comp_conj" "Unexpected match case (1)."
    else
      let left_op_list, _ = Base.List.unzip exprs in
      match (top_op, op) with
      | Or, Lt | Or, Le | And, Gt | And, Ge ->
          FnBinop (op, FnApp (type_of common_expr, Some (get_AC_op Min), left_op_list), common_expr)
      | And, Lt | And, Le | Or, Gt | Or, Ge ->
          FnBinop (op, FnApp (type_of common_expr, Some (get_AC_op Max), left_op_list), common_expr)
      | _, _ -> failhere __FILE__ "build_comp_conj" "Unexpected match case (2)."
  in
  (* Regroup expressions in expression list. Check for factorizable terms while
     regrouping: the list of expressions get modified during the regroup phase. *)
  let rec regroup_comp_conj op el =
    match el with
    | (e1, e2) :: tl ->
        let left_common, left_tl_rest = List.partition (fun (e1', _) -> e1 @= e1') tl in
        let right_common, right_tl_rest = List.partition (fun (_, e2') -> e2 @= e2') tl in
        let hdexpr, new_tl =
          if List.length left_common > 0 || List.length right_common > 0 then
            if List.length left_common > List.length right_common then
              (build_comp_conj true top_op op e1 ((e1, e2) :: left_common), left_tl_rest)
            else (build_comp_conj false top_op op e2 ((e1, e2) :: right_common), right_tl_rest)
          else (FnBinop (op, e1, e2), tl)
        in
        hdexpr :: regroup_comp_conj op new_tl
    | [] -> []
  in
  let regroup_operands el =
    (* el is a list of expressions FnBinop(op, e1, e2) where op is a comparison operator.
       First, group each that have the same comparions operator. *)
    let opmap =
      List.fold_left
        (fun bmap expr ->
          match expr with FnBinop (op, e1, e2) -> update_assocmap op (e1, e2) bmap | _ -> bmap)
        BinopMap.empty el
    in
    let res = BinopMap.bindings (BinopMap.mapi regroup_comp_conj opmap) in
    List.flatten (ListTools.lsnd res)
  in
  List.map flatten_AC (rest @ regroup_operands with_comparison)

let transform_conj_comps e =
  let case e =
    match e with
    | FnApp (_, Some vi, _) when vi.vname = "and" || vi.vname = "or" -> true
    | _ -> false
  in
  let transf rfunc e =
    match e with
    | FnApp (t, Some vi, el) -> (
        let el' = List.map rfunc el in
        let op = check_option (op_from_name vi.vname) in
        let new_el = __transform_conj_comps__ op el' in
        match new_el with [ e ] -> e | _ -> FnApp (t, Some vi, new_el))
    | _ -> failwith "Not a valid case."
  in
  transform_expr case transf identity identity e

(** Put all the special rules here *)
let apply_special_rules (ctx : context) (e : fnExpr) : fnExpr =
  let e0 = transform_all_comparisons e in
  let e1 =
    let e'' = transform_conj_comps e0 in
    let e' = factorize ctx e'' in
    if cost ctx e' < cost ctx e0 then e' else if cost ctx e'' < cost ctx e0 then e'' else e0
    (* e' *)
  in
  factorize ctx e1

let accumulated_subexpression vi e =
  let is_int_const c =
    match c with
    | FnConst (CInt j) -> (true, j)
    | FnConst (CInt64 j) -> (true, Int64.to_int j)
    | _ -> (false, -1)
  in
  match e with
  | FnBinop (_, FnVar (FnVariable vi'), acc) when vi = vi' -> (acc, 0)
  | FnBinop (_, acc, FnVar (FnVariable vi')) when vi = vi' -> (acc, 0)
  | FnBinop (_, FnVar (FnArray (FnVariable vi', c)), acc)
  | FnBinop (_, acc, FnVar (FnArray (FnVariable vi', c))) ->
      let cond, j = is_int_const c in
      if vi = vi' && cond then (acc, j) else (e, 0)
  | _ -> (e, 0)

(** Transformations taking AC in account *)
let replace_AC ctx ~to_replace ~by:by_expr ~ine:in_expr =
  let flat_tr = flatten_AC to_replace in
  let flat_by = flatten_AC by_expr in
  let flat_in = flatten_AC in_expr in
  let case = function
    | FnApp (_, Some opvar, _) -> (
        try
          ignore (op_from_name opvar.vname);
          true
        with Not_found -> false)
    | e when e @= flat_tr -> true
    | _ -> false
  in
  let handle_case rfunc = function
    | FnApp (t, Some opvar, el) -> (
        let op = op_from_name opvar.vname in
        match flat_tr with
        | FnApp (_, Some opvar', el') ->
            let op' = op_from_name opvar'.vname in
            if op = op' then
              (* Split the super list in terms shared by the expression to
                 replace and other expressions *)
              let common_terms, remaining_terms = List.partition (fun e -> List.mem e el') el in
              (* To have a matchimg expression all the terms in the term to
                 replace must be in the super term *)
              let common_is_el' = List.for_all (fun e -> List.mem e common_terms) el' in
              if common_is_el' then
                let raw_term = FnApp (t, Some opvar, remaining_terms @ [ flat_by ]) in
                flatten_AC (rebuild_tree_AC ctx raw_term)
              else FnApp (t, Some opvar, List.map rfunc el) (* END if common_is_el' *)
            else FnApp (t, Some opvar, List.map rfunc el)
        (* END if op = op' *)
        | _ -> FnApp (t, Some opvar, List.map rfunc el))
    | e when e @= flat_tr -> flat_by
    | _ -> failwith "Unexpected case in replace_AC"
  in
  rebuild_tree_AC ctx (transform_expr case handle_case identity identity flat_in)

let replace_many_AC ?(_in_subscripts = false) ~to_replace:tr ~by:b expr n =
  (* Count how many expressions have to be replaced, and then using a mutable
     counter replace expressions depending on counter. For each possible
     combination, give the indexes that have to be replaced. *)
  let num_occ =
    rec_expr2
      {
        init = 0;
        join = (fun a b -> a + b);
        case = (fun e -> e @= tr);
        on_case = (fun _ _ -> 1);
        on_var = (fun _ -> 0);
        on_const = (fun _ -> 0);
      }
      expr
  in
  let repl_indexed il =
    let cntr = ref 0 in
    transform_expr2
      {
        case = (fun e -> e @= tr);
        on_var = (fun v -> v);
        on_case =
          (fun _ e ->
            incr cntr;
            if List.mem !cntr il then b else e);
        on_const = (fun c -> c);
      }
      expr
  in
  if num_occ <= 0 then [ expr ]
  else
    let index_to_repl = k_combinations n (1 -- num_occ) in
    List.map repl_indexed index_to_repl

let enormalize (ctx : context) (expr : fnExpr) : fnExpr =
  let one_step = flatten_AC --> normalize_AC --> rebuild_tree_AC ctx --> peval in
  one_step (one_step expr)
