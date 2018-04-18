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

open Format
open FPretty
open FuncTypes
open TestUtils
open Utils

(** Hashtable string -> 'a *)

let rec hash_str s =
  if String.length s > 0 then
    (int_of_char (String.get s 0)) +
    (hash_str (String.sub s 1 ((String.length s)- 1))) * 10
  else
    0

module SH = Hashtbl.Make
    (struct type t = string let compare = String.compare
      let equal s s' = s = s'
      let hash s = hash_str s
    end)




(** List different types of operators:
    - comparison operators
    - associative operators
    - commutative operators

    And properties:
    - left and right distributivity.
*)

let comparison_operators : symb_binop list = [Gt; Ge; Lt; Le]
let associative_operators = [And; Or; Plus; Max; Min; Times]
let commutative_operators = [And; Or; Plus; Max; Min; Times; Eq; Neq]

let is_associative op = List.mem op associative_operators
let is_commutative op = List.mem op commutative_operators

let is_right_distributive op1 op2 =
  (** (a op1 b) op2 c = (a op2 c) op1 (b op2 c) *)
  match op1, op2 with
  | Or, And
  | Min, Plus
  | Max, Plus
  | Plus, Times -> true
  | _, _ ->  false

let is_left_distributive op1 op2 =
  (**  a op2 (b op1 c) = (a op1 b) op2 (a op1 c) *)
  match op1, op2 with
  | Plus, Times
  | Max, Plus
  | Min, Plus
  | Or, And -> true
  | _ , _ -> false

(** Operator -> variable *)
let int_function = Function (List (Integer, None), Integer)
let bool_function = Function (List (Boolean, None), Boolean)

let named_AC_ops = SH.create 10;;
(** Initialize map *)
SH.add named_AC_ops "plus" (mkFnVar "plus" int_function);
SH.add named_AC_ops "times" (mkFnVar "times" int_function);
SH.add named_AC_ops "max" (mkFnVar "max" int_function);
SH.add named_AC_ops "min" (mkFnVar "min" int_function);
SH.add named_AC_ops "and" (mkFnVar "and" bool_function);
SH.add named_AC_ops "or" (mkFnVar "or" bool_function);;


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

let op_from_name name =
  match name with
  | "plus" -> Plus
  | "times" -> Times
  | "and" -> And
  | "or" -> Or
  | "min" -> Min
  | "max" -> Max
  | _ -> raise Not_found


(** Identity rules *)
let operators_with_identities : symb_binop list = [Minus; Plus; Times; Div]

let apply_right_identity op t e =
  if t = Integer || t = Real || t = Num then (_b e op sk_zero) else e
  (*   match op with *)
  (*   | Plus | Minus -> _b e op sk_zero *)
  (*   | Times | Div -> _b e op sk_one *)
  (*   | _ -> e *)
  (* else e *)
let apply_left_identity op t e = e
  (* if t = Integer || t = Real || t = Num then *)
  (*   match op with *)
  (*   | Plus -> _b sk_zero op e *)
  (*   | Times | Div -> _b sk_one op e *)
  (*   | _ -> e *)
  (* else e *)
(** Flatten trees with a AC spine. Expressions are encoded via function
    applications : the function is named after the operator in the stringhash
    above.
*)
let rec flatten_AC expr =
  let rec flatten cur_op expr =
    match expr with
    | FnBinop (op, e1, e2) when op = cur_op ->
      (flatten cur_op e1)@(flatten cur_op e2)
    | e -> [flatten_AC e]
  in
  let filter_exprs e =
      match e with
        | FnBinop (op, e1, e2)
          when is_associative op && is_commutative op -> true
        | _ -> false
  in
  let flatten_expr rfunc e =
    match e with
    | FnBinop (op, e1, e2) when is_associative op && is_commutative op ->
      let operands = (flatten op e1)@(flatten op e2) in
      assert (List.length operands > 0);
      let func_vi = get_AC_op op in
      FnApp (Integer, Some func_vi, operands)
    | _ -> rfunc e
  in
  transform_expr filter_exprs flatten_expr identity identity expr



(** Equality under associativity and commutativity. Can be defined
    as structural equality of expressions trees with reordering in flat
    terms *)
let ( @= ) e1 e2 =
  let rec aux_eq e1 e2=
  match e1, e2 with
  | FnBinop (op1, e11, e12), FnBinop (op2, e21, e22) ->
    let strict_equal = op1 = op2 && aux_eq e11 e21 && aux_eq e12 e22 in
    let comm_eq = op1 = op2 && is_commutative op1 &&
                  aux_eq e11 e22 && aux_eq e12 e21
    in
    strict_equal || comm_eq

  | FnUnop (op1, e11), FnUnop (op2, e21) ->
    op1 = op2 && aux_eq e11 e21

  | FnApp (t1, Some v1, el1), FnApp (t2, Some v2, el2) ->
    if v1 = v2 then
      try
        let op = op_from_name v1.vname in
        is_commutative op &&
        List.length el1 = List.length el2 &&
        (List.for_all
           (fun elt1 ->
              List.exists (fun elt2 -> aux_eq elt1 elt2) el2)
           el1)
        &&
        (List.for_all
           (fun elt2 ->
              List.exists (fun elt1 -> aux_eq elt1 elt2) el1)
           el2)

      with Not_found ->
        el1 = el2
    else
      false

  | FnQuestion (c1, e11, e12), FnQuestion (c2, e21, e22) ->
    aux_eq c1 c2 && aux_eq e11 e21 && aux_eq e12 e22

  | _, _ -> e1 = e2
  in
  aux_eq (flatten_AC e1) (flatten_AC e2)


(* Set of expressions, equipped with the associative and commutative
   equality.
 *)
module ACES = Set.Make (
  struct
    type t = fnExpr
    let compare x y =
      (if x @= y then 0 else 1)
  end)

let es_to_aces s = ACES.of_list (ES.elements s)


let update_assoc_ace al (op, a) b =
  match
    (List.fold_left
      (fun (found, nl) ((op', a'),b') ->
         if a' @= a && op' = op then (true, ((op, a), b::b')::nl)
         else (found, ((op', a'),b')::nl))
      (false, [])
      al) with
  | true, nl -> nl
  | false, nl -> ((op, a),[b])::nl

(* Expression cost: the number of occurrences of
   an expression and the maximal depth of an expression. *)
type ecost =
  {
    occurrences : int;
    max_depth : int;
  }

let expression_cost ctx e =
  let ctx_costlies = es_to_aces ctx.costly_exprs in
  let case0 = { occurrences = 0; max_depth = 0 } in
  let case1 = { occurrences = 1; max_depth = 1 } in
  let join_c c1 c2 =
    { occurrences = c1.occurrences + c2.occurrences;
      max_depth = let mx =  max c1.max_depth c2.max_depth in
        if mx > 0 then mx + 1 else 0 }
  in
  let special_case e = ACES.mem e ctx_costlies in
  let handle_spec f e =  case1 in
  let case_var v =
    let vi_o = vi_of v in
    match vi_o with
    | Some vi -> if VarSet.mem vi ctx.state_vars then case1 else case0
    | _ -> case0
  in
  let case_const c = case0 in
  rec_expr join_c case0 special_case handle_spec case_const case_var e

let ccost (d1, o1) (d2, o2) =
  if d1 = d2 then compare o1 o2 else compare d1 d2

let compare_ecost ec1 ec2 =
  ccost (ec1.max_depth, ec1.occurrences) (ec2.max_depth, ec2.occurrences)

let compare_cost ctx e1 e2 =
  compare_ecost (expression_cost ctx e1) (expression_cost ctx e2)


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
      (List.fold_left
         (fun (mde, sec) (de, ec) -> (max mde de, sec + ec))
         (0, 0)
         (List.map (fun (v, e) -> depth_cost ctx e) velist)) in
    ((max max_de (if dl' > 0 then dl' + 1 else 0)), sum_c + cl')
  | FnLetExpr velist ->
    (List.fold_left
       (fun (mde, sec) (de, ec) -> (max mde de, sec + ec))
       (0, 0)
       (List.map (fun (v, e) -> depth_cost ctx e) velist))
  | _ -> (0,0)

let cost ctx expr =
  depth_cost ctx expr




(* AC rules *)

let e_of_ac_op e =
  match e with
  | FnApp(t, Some f, el) -> SH.mem named_AC_ops f.vname
  | _ -> false

let op_of_ac_e e =
  match e with
  | FnApp(t, Some f, el) ->
    Some (op_from_name f.vname)
  | _ -> None

let args_of_ac_e e =
  match e with
  | FnApp(_,_,el) when e_of_ac_op e -> Some el
  | _ -> None

(* Rebuild an expression from its flattened expression. *)
let rec rebuild_tree_AC ctx =
  let rebuild_flat_expr rfunc e =
    match e with
    | FnApp (t, Some f, el) ->
      begin
        let op = op_from_name f.vname in
        let el' = List.map rfunc el in
        let el_ordered =
             (List.sort (compare_cost ctx) el')
        in
        match el_ordered with
        | hd :: tl ->
          List.fold_left
            (fun tree e -> FnBinop (op, e, tree))
            hd tl
        | [] -> failhere __FILE__ "rebuild_tree_AC"
                  "Unexpected length for list in AC conversion"
      end

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
    (fun e -> match e with
       | FnVar (FnArray (FnVariable a, _)) -> Some a
       | _ -> None)
    (ES.elements ctx.costly_exprs)

let costly_vars ctx =
  ListTools.mapoption
    (fun e -> match e with
       | FnVar (FnVariable a)  -> Some a
       | _ -> None)
    (ES.elements ctx.costly_exprs)

type expression_flavour =
  | Normal
  | State
  | Input
  | Const
  | NonNormal

let locality_rule ctx e =
  let cvs =  VarSet.of_list (costly_vars ctx) in
  let ctas = VarSet.of_list (costly_arrays ctx) in
  rec_expr2
    {
      join = (fun f1 f2 ->
          match f1, f2 with
          | e1, e2 when e1 = e2 -> e1
          | State, Input -> Normal
          | Input, State -> Normal
          | Normal, Normal -> Normal
          | Const, e1 | e1, Const -> e1
          | _, _ -> NonNormal
        );
      init = Normal;
      case = (fun e -> false);
      on_case = (fun e f -> Normal);
      on_var =
        (fun v ->
           match v with
           | FnArray (FnVariable c, _) ->
             if VarSet.mem c ctas then State else Input
           | FnVariable v ->
             if VarSet.mem v cvs then State else Input
           | _ -> Input
        );
      on_const = (fun c -> Const);
    } e

let is_normal =
  function
  | NonNormal -> false
  | _ -> true

let collect_normal_subexpressions ctx =
  rec_expr2
    {
      join = (fun x y -> x @ y);
      init = [];
      case = (fun e ->
          match e with
          | FnBinop _ | FnUnop _ | FnCond _ ->
            true
          | _ ->  false);
      on_case =
        (fun f e ->
           if is_normal (locality_rule ctx e) then [e] else
             match e with
             | FnBinop (_, e1, e2) -> (f e1)@(f e2)
             | FnUnop (_, e1) -> (f e1)
             | FnCond (_, e1, e2) -> (f e1)@(f e2)
             | _ -> failhere __FILE__ "collect" "x"
             );
      on_var =
        (fun v -> [FnVar v]);
      on_const =
        (fun c -> [FnConst c]);
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
      (fun e -> match op_of_ac_e e with
         | Some op -> is_right_distributive top_op op
         | None -> false) el
  in
  (* Transforms the list into a binary expression containing
     on one side the state variables, the other side other variables.
  *)
  let split_e =
    List.map
      (fun e -> match e with
         | FnApp (t, f, args) ->
           let args1, args2 =
             List.partition
               (fun e -> ACES.mem e ac_costlies) args
           in
           let op = check_option (op_of_ac_e e) in
           (match List.length args1, List.length args2 with
            (* Initial list was empty? *)
            | 0, 0 -> e
            (* No 'costly' expression in the arguments. *)
            | 0 , _ -> e
            (* All arguments are 'costly' *)
            | _ , 0 -> e
            (* Costly part needs to be separated from inputs.
               Create a binary expression, with the first operand always
               being the operand containing the costly expressions.
            *)
            | _, _ ->
              FnBinop
                (op, FnApp (t,f,args1), FnApp (t,f,args2)))
         | _ -> e)
      el_hasop
  in
  let new_factorized_expr =
    let factor_assoc_list, rest =
      List.fold_left
        (fun (alist, rst) e ->
           match e with
           | FnBinop (op, ecostly, echeap) ->
             (update_assoc_ace alist (op, ecostly) echeap, rst)
           | _ -> (alist, e::rst)
        )
        ([], [])
        split_e
    in
    let factorized =
      List.map
         (fun ((op, a), bl) ->
            if List.length bl > 1 then
              FnBinop (op, a, FnApp(type_of (bl >> 0), Some (get_AC_op top_op), bl))
            else
              FnBinop (op, a, (bl >> 0)))
         factor_assoc_list
    in
    factorized@rest
  in
  (new_factorized_expr@el_noop)


let factorize_multi_toplevel ctx e =
  (* Transform apps where we can recognize the top operator. *)
  let e' = flatten_AC e in
  let eres =
    match e' with
    | FnApp (t, Some op, el) ->
      FnApp(t, Some op, __factorize_multi__ ctx (op_from_name op.vname) el)
    | e -> e'
  in
  let e'' =  rebuild_tree_AC ctx eres in
  e''

(** Inverse distributivity / factorization.
    This step rebuilds expression trees, but has to flatten the expressions
    it returns *)
let extract_operand_lists el =
  List.fold_left
    (fun (l1, l2) e ->
       match e with
       | FnBinop (_, e1, e2) -> (l1@[e1], l2@[e2])
       | _ -> l1, l2)
    ([], []) el

let __factorize__ ctx top_op el =
  let el = List.map (rebuild_tree_AC ctx) el in
  let el_binops, el_no_binops =
    List.partition (function | FnVar v -> true
                             | FnBinop (_, _, _) -> true
                             | _ -> false) el
  in
  (* Regroup expressions lists by common factors.
  *)
  let rec regroup el =
    match el with
    | hd :: tl ->
      begin (** begin match list *)
        match hd with
        | FnBinop (op, e1, e2) ->
          let ce1 = cost ctx e1 in
          let ce2 = cost ctx e2 in

          if is_left_distributive top_op op && ce1 > ce2 then
            (** Look for similar expressions in the list *)
            let sim_exprs, rtl =
              List.partition
                (fun e ->
                   match e with
                   | FnBinop (op', e1', ee) when op' = op && e1' @= e1 -> true
                   (* | FnBinop (op', ee, e1') when op' = op && e1' @= e1 && is_commutative op' ->
                    *   true *)
                   | _ -> false) tl

            in
            let _, sim_exprs_snd = extract_operand_lists sim_exprs in
            let new_exprs =
              FnBinop
                (op,
                 e1,
                 FnApp (type_of e2, Some (get_AC_op top_op), e2::sim_exprs_snd))
            in
            new_exprs::(regroup rtl)

          else

            begin

              if is_right_distributive top_op op && ce2 < ce1 then
                let sim_exprs, rtl =
                  List.partition
                    (fun e ->
                       match e with
                       | FnBinop (op', ee, e2') when
                           op' = op && e2' @= e2 -> true
                       | _ -> false) tl
                in
                (* Extract the list of the second operands of the list of
                   binary operators *)
                let sim_exprs_fst, _ = extract_operand_lists sim_exprs in
                (* Build the new expression by lifting e2 on top at the
                   right of the operator *)
                let new_exprs =
                  FnBinop
                    (op,
                     FnApp (type_of e1, Some (get_AC_op top_op), e1::sim_exprs_fst),
                     e2)
                in
                new_exprs::(regroup rtl)

              else
                hd::(regroup tl)
            end

        | _ ->  hd::(regroup tl)
      end (** end match hd::tl *)
    | [] -> []
  in
  let applied_different_right_identities =
    List.map
      (fun op ->
         List.map
           (fun e ->
              match e with
              | FnVar v -> apply_right_identity op (type_of e) e
              | _ -> e)
           el_binops)
      operators_with_identities
  in
  let applied_different_left_identities =
    List.map
      (fun op ->
         List.map
           (fun e ->
              match e with
              | FnVar v -> apply_left_identity op (type_of e) e
              | _ -> e)
           el_binops)
      operators_with_identities
  in
  let different_factorizations =
    List.map regroup ( applied_different_left_identities @
                      applied_different_right_identities @
                      [el_binops])
  in
  let best_factorization =
    ListTools.lmin List.length different_factorizations
  in
  List.map flatten_AC (best_factorization @(el_no_binops))

let factorize ctx =
  (* Transform apps where we can recognize the top operator. *)
  let case e =
    match e with
    | FnApp (_, Some opvar, _) ->
      (try ignore(op_from_name opvar.vname); true with Not_found -> false)
    | _ -> false
  in
  let fact rfunc e =
    match e with
    | FnApp (t, Some opvar, el) ->
      let op = op_from_name opvar.vname in
      let fact_el = List.map rfunc (__factorize__ ctx op el) in
      FnApp (t, Some opvar, fact_el)

    | _ -> failhere __FILE__ "factorize_all" "bad case"
  in
  transform_expr case fact identity identity


(** Transform all comparisons : Lt -> Gt Le -> Ge *)
let transform_all_comparisons expr =
  let case e =
    match e with
    | FnBinop (cop, _, _) ->
      (match cop with
       | Lt | Le -> true
       | _ -> false)
    | _ -> false
  in
  let transformer rfunc e =
    match e with
    | FnBinop (cop, e1, e2) ->
      (match cop with
       | Lt -> FnBinop (Gt, rfunc e1, rfunc e2)
       | Le -> FnBinop (Ge, rfunc e1, rfunc e2)
       | _ -> failwith "Not a special recursive case")
    | _ -> failwith "Not a special recursive case"
  in
  transform_expr case transformer identity identity expr


let __transform_conj_comps__ top_op el =
  let with_comparison, rest =
    List.partition
      (fun e ->
         match e with
         | FnBinop (op, _, _) -> List.mem op comparison_operators
         | _ -> false) el
  in
  (* Build max or min from conjunctions of comparisons.
     Rules:
     + a > b and c > b <=> min(a,c) > b.
     + a > b or c > b <=> max(a,c) > b.
  *)
  let build_comp_conj
      (is_left_operand : bool)
      (top_op : symb_binop)
      (op : symb_binop) common_expr exprs =
    if is_left_operand then
      let _, right_op_list = extract_operand_lists exprs in
      match top_op, op with
      | Or, Lt | Or, Le | And, Gt | And, Ge  ->
        FnBinop(op,
                common_expr,
                FnApp (type_of common_expr, Some (get_AC_op Max),
                       right_op_list))

      | And, Lt | And, Le | Or, Gt | Or, Ge ->
        FnBinop(op,
                common_expr,
                FnApp (type_of common_expr, Some (get_AC_op Min),
                       right_op_list))

      | _ , _ -> failhere __FILE__ "build_comp_conj" "Unexpected match case (1)."
    else
      let left_op_list, _ = extract_operand_lists exprs in
      match top_op, op with
      | Or, Lt | Or, Le | And, Gt | And, Ge  ->
          FnBinop(op,
                  FnApp (type_of common_expr, Some (get_AC_op Min),
                         left_op_list),
                  common_expr)

      | And, Lt | And, Le | Or, Gt | Or, Ge ->
        FnBinop(op,
                FnApp (type_of common_expr, Some (get_AC_op Max),
                       left_op_list),
                common_expr)

      | _ , _ -> failhere __FILE__ "build_comp_conj" "Unexpected match case (2)."
  in
  (* Regroup expressions in expression list. Check for factorizable terms while
     regrouping: the list of expressions get modified during the regroup phase. *)
  let rec regroup el =
    match el with
    | hd :: tl ->
      begin
        match hd with
        | FnBinop (op, e1, e2) ->
          let left_common, left_tl_rest =
            List.partition
              (fun e ->
                 match e with
                 | FnBinop (op', e1', e2') -> op' = op && e1 @= e1'
                 | _ -> false)
              tl
          in
          let right_common, right_tl_rest =
            List.partition
              (fun e ->
                 match e with
                 | FnBinop (op', e1', e2') -> op' = op && e2 @= e2'
                 | _ -> false)
              tl
          in
          let hdexpr, new_tl =
            if List.length left_common > 0 || List.length right_common > 0 then
              begin
                if List.length left_common > List.length right_common
                then
                  build_comp_conj true top_op op e1 (hd::left_common),
                  left_tl_rest
                else
                  build_comp_conj false top_op op e2 (hd::right_common),
                  right_tl_rest
              end
            else
              hd, tl
          in
          hdexpr::(regroup new_tl)

        | _ -> failwith "Unexpected case in regroup el"
      end

    | [] -> []

  in
  List.map flatten_AC (rest@(regroup with_comparison))

let transform_conj_comps e =
  let case e =
    match e with
    | FnApp (_, Some vi, _) when vi.vname = "and" || vi.vname = "or" -> true
    | _ -> false
  in
  let transf rfunc e =
    match e with
    | FnApp (t, Some vi, el) ->
      let el' = List.map rfunc el in
      let op = op_from_name vi.vname in
      let new_el = __transform_conj_comps__  op el' in
      (match new_el with
       | [e] -> e
       | _ ->
         FnApp (t, Some vi, new_el))

    | _ -> failwith "Not a valid case."
  in
  transform_expr case transf identity identity e

(** Put all the special rules here *)
let apply_special_rules ctx e =
  let e0 = transform_all_comparisons e in
  let e1 =
    let e' = factorize ctx (transform_conj_comps e) in
    if cost ctx e' < cost ctx e0 then e' else e0
  in
  factorize ctx e1

let accumulated_subexpression vi e =
  match e with
  | FnBinop (op, FnVar (FnVariable vi'), acc) when vi = vi' -> acc
  | FnBinop (op, acc, FnVar (FnVariable vi')) when vi = vi' -> acc
  | _ -> e


(** Transformations taking AC in account *)
let replace_AC ctx ~to_replace:to_replace ~by:by_expr ~ine:in_expr =
  let flat_tr = flatten_AC to_replace in
  let flat_by = flatten_AC by_expr in
  let flat_in = flatten_AC in_expr in
  let case =
    function
    | FnApp (_, Some opvar, _) ->
      (try ignore(op_from_name opvar.vname); true with Not_found -> false)
    | e when e @= flat_tr -> true
    | _ -> false
  in
  let handle_case rfunc =
    function
    | FnApp (t, Some opvar, el) ->
      let op = op_from_name opvar.vname in
      begin
        match flat_tr with
        | FnApp (t', Some opvar', el') ->
          let op' = op_from_name opvar'.vname in
          if op = op' then
            begin
              (* Split the super list in terms shared by the expression to
                 replace and other expressions *)
              let common_terms, remaining_terms =
                List.partition
                  (fun e -> List.mem e el') el
              in
              (* To have a matchimg expression all the terms in the term to
                 replace must be in the super term *)
              let common_is_el' =
                List.for_all (fun e -> List.mem e common_terms) el' in
              begin
                if common_is_el' then
                  let raw_term = FnApp (t, Some opvar, remaining_terms@[flat_by]) in
                  flatten_AC (rebuild_tree_AC ctx raw_term)
                else
                  FnApp (t, Some opvar, List.map rfunc el)
              end (* END if common_is_el' *)
            end
          else
            FnApp (t, Some opvar, List.map rfunc el)
    (* END if op = op' *)
    | _ -> FnApp (t, Some opvar, List.map rfunc el)
end
| e when e @= flat_tr -> flat_by
       | _ -> failwith "Unexpected case in replace_AC"
in
rebuild_tree_AC ctx (transform_expr case handle_case identity identity flat_in)


(* Other expression properties *)
let is_constant expr =
  rec_expr2
    { join = (fun a b -> a && b) ;
      init = true;
      case = (fun e -> false);
      on_case = (fun f e -> true);
      on_const = (fun c -> true);
      on_var = (fun v -> false);
    }
    expr
