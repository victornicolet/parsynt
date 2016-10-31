open SketchTypes
open Cil
open Utils


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
  | Or, And -> true
  | _ , _ -> false

(** Operator -> variable *)
let c_t_int = TInt (IInt, [])
let c_t_bool = TInt (IBool, [])

let named_AC_ops = SH.create 10;;
(** Initialize map *)
SH.add named_AC_ops "plus"
  (makeVarinfo false "plus"
     (TFun (c_t_int,
            Some [("x", c_t_int, []); ("y", c_t_int, [])], false, [])));

SH.add named_AC_ops "times"
  (makeVarinfo false "times"
     (TFun (c_t_int,
            Some [("x", c_t_int, []); ("y", c_t_int, [])], false, [])));

SH.add named_AC_ops "max"
  (makeVarinfo false "max"
     (TFun (c_t_int,
            Some [("x", c_t_int, []); ("y", c_t_int, [])], false, [])));

SH.add named_AC_ops "min"
  (makeVarinfo false "min"
     (TFun (c_t_int,
            Some [("x", c_t_int, []); ("y", c_t_int, [])], false, [])));

SH.add named_AC_ops "and"
  (makeVarinfo false "and"
     (TFun (c_t_bool,
            Some [("x", c_t_bool, []); ("y", c_t_bool, [])], false, [])));

SH.add named_AC_ops "or"
  (makeVarinfo false "or"
     (TFun (c_t_bool,
            Some [("x", c_t_bool, []); ("y", c_t_bool, [])], false, [])));;

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

(** Flatten trees with a AC spine. Expressions are encoded via function
    applications : the function is named after the operator in the stringhash
    above.
*)
let rec flatten_AC expr =
  let rec flatten cur_op expr =
    match expr with
    | SkBinop (op, e1, e2) when op = cur_op ->
      (flatten cur_op e1)@(flatten cur_op e2)
    | e -> [flatten_AC e]
  in
  let filter_exprs e =
      match e with
        | SkBinop (op, e1, e2)
          when is_associative op && is_commutative op -> true
        | _ -> false
  in
  let flatten_expr rfunc e =
    match e with
    | SkBinop (op, e1, e2) when is_associative op && is_commutative op ->
      let operands = (flatten op e1)@(flatten op e2) in
      assert (List.length operands > 0);
      let func_vi = get_AC_op op in
      SkApp (Integer, Some func_vi, operands)
    | _ -> rfunc e
  in
  transform_expr filter_exprs flatten_expr identity identity expr



(** Equality under associativity and commutativity. Can be defined
    as structural equality of expressions trees with reordering in flat
    terms *)
let eq_AC e1 e2 = (flatten_AC e1) = (flatten_AC e2)

(** Find similar terms in a flat expressions that can be factored *)
let unifiy_AC e = e

type ecost =
  {
    occurrences : int;
    max_depth : int;
  }

let expression_cost vs cexprs e =
  let case0 = { occurrences = 0; max_depth = 0 } in
  let case1 = { occurrences = 1; max_depth = 1 } in
  let join_c c1 c2 =
    { occurrences = c1.occurrences + c2.occurrences;
      max_depth = let mx =  max c1.max_depth c2.max_depth in
        if mx > 0 then mx + 1 else 0 }
  in
  let special_case e = ES.mem e cexprs in
  let handle_spec e =  case1 in let case_var v = case1 in
  let case_const c = case0 in
  rec_expr join_c case0 special_case handle_spec case_const case_var e

let ccost (d1, o1) (d2, o2) =
  if d1 = d2 then compare o1 o2 else compare d1 d2

let compare_ecost ec1 ec2 =
  ccost (ec1.max_depth, ec1.occurrences) (ec2.max_depth, ec2.occurrences)

let compare_cost vs cexprs e1 e2 =
  compare_ecost (expression_cost vs cexprs e1) (expression_cost vs cexprs e2)

let rec rebuild_tree_AC vs cexprs =
  let rebuild_case expr =
    match expr with
    | SkApp (t, Some f, el) ->
      SH.mem named_AC_ops f.vname
    | _ -> false
  in
  let rebuild_flat_expr rfunc e =
    match e with
    | SkApp (t, Some f, el) ->
      begin
        let op = op_from_name f.vname in
        let el' = List.map rfunc el in
        let el_ordered =
          (List.rev
             (List.sort (compare_cost vs cexprs) el'))
        in
        match el_ordered with
        | hd :: tl ->
          List.fold_left
            (fun tree e -> SkBinop (op, e, tree))
            hd tl
        | [] -> failwith "Unexpected length for list in AC conversion"
      end

    | _ -> failwith "Rebuild_flat_expr : Unexpected case."
  in
  transform_expr rebuild_case rebuild_flat_expr identity identity
(** SPecial rules, tranformations. *)

(** Transform all comparisons : Lt -> Gt Le -> Ge *)
let transform_all_comparisons expr =
  let case e =
    match e with
    | SkBinop (cop, _, _) ->
      (match cop with
       | Lt | Le -> true
       | _ -> false)
    | _ -> false
  in
  let transformer rfunc e =
    match e with
    | SkBinop (cop, e1, e2) ->
      (match cop with
       | Lt -> SkBinop (Gt, rfunc e1, rfunc e2)
       | Le -> SkBinop (Gt, rfunc e1, rfunc e2)
       | _ -> failwith "Not a special recursive case")
    | _ -> failwith "Not a special recursive case"
  in
  transform_expr case transformer identity identity expr

let extract_operand_lists el =
  List.fold_left
    (fun (l1, l2) e ->
       match e with
       | SkBinop (_, e1, e2) -> (l1@[e1], l2@[e2])
       | _ -> l1, l2
    ) ([], []) el


let conjunction_comparison_to_max el =
  let comp_op, ec1, ec2 =
    (match List.nth el 0 with
    | SkBinop (op, ec1, ec2) -> Some op, Some ec1, Some ec2
    | _ -> None, None, None)
  in
  match comp_op with
  | Some cop ->
    begin
      let is_comp_conjunction =
        List.for_all
          (fun e ->
             match e with
             | SkBinop (op, _, _) when op = cop -> true
             | _ -> false)
          el
      in
      let first_operands, second_operands =
        extract_operand_lists el
      in
      let first_op_constant, second_op_constant =
        List.for_all
          (fun e -> (match e with | SkBinop (_, e1, _) ->
               eq_AC e1 (check_option ec1) | _ -> false)) el,
        List.for_all
          (fun e -> (match e with | SkBinop (_, _, e2) ->
               eq_AC e2 (check_option ec2) | _ -> false)) el
      in
      match is_comp_conjunction, first_op_constant, second_op_constant with
      | true, true, false ->
        SkBinop (cop, check_option ec1,
                 SkApp (Boolean, Some (get_AC_op Min), second_operands))

      | true, false, true ->
        SkBinop (cop,
                 SkApp (Boolean, Some (get_AC_op Max), first_operands ),
                 check_option ec2)

      | true, true, true ->
        SkBinop (cop, check_option ec1, check_option ec2)

      | _ -> SkApp (Boolean, Some (get_AC_op And), el)
    end
  | None ->  SkApp (Boolean, Some (get_AC_op And), el)
