open Utils
open Cil

(** ------------------------------------------------------------------*)
(** Type for intermediary representation of the loop body *)
(** The loop body is a Inthash from the state variable ids 
    to an expression of type preFunc *)
(** Short functional representation *)
type preFunc = 
  | Empty
  (** A cil expression *)
  | Container of Cil.exp
  | FBinop of Cil.binop * preFunc * preFunc
  | FUnop of Cil.unop * preFunc
  (** 
      A loop enclosing an assignment is reduced to the IGU,
      the subscripts if is is an array and the right-hand side
      expression in the assignment.
      The subscript expression list is empty if it is a scalar.
  *)
  (** init, igu, subscripts, expression *)
  | ForLoop of preFunc * Loops.forIGU * Cil.exp list * preFunc
  (* An expression guarded by an if *)
  | Guarded of preFunc * preFunc * preFunc

(** 
    Some types to record the control statements above 
    an expression
*)

type guard =
    GEmpty 
  | GCond of Cil.exp * guard
  | GFor of Loops.forIGU * guard


(** ------------------------------------------------------------------*)
(** Utilities for the types *)

let rec gcompose g1 g2 =
  match g1 with
  | GEmpty -> g2
  | GCond (e, g) -> GCond (e, gcompose g g2)
  | GFor (igu, g) -> GFor (igu, gcompose g g2)


let rec build ?(subs= [])  g (expr : Cil.exp) (x : Cil.varinfo)=
  match g with
  | GEmpty -> Container expr
  | GCond (e, g') -> Guarded (Container e, 
                              (build g' expr x),
                              Container (v2e x))
  | GFor (igu, g') -> 
     ForLoop (Container (v2e x), igu, subs, build g' expr x)


let rec rep vid old ne =
  match ne with
  | Empty -> Empty
  | Container e -> (rep_in_e vid old e)
  | FBinop (op, e1, e2) -> FBinop (op, rep vid old e1, rep vid old e2)
  | FUnop (op, e) -> FUnop (op, rep vid old e)
  | ForLoop (init, e, el, g) -> ForLoop (rep vid old init, e, el, g)
  | Guarded (e, g1, g2) -> Guarded (e, rep vid old g1,
                                    rep vid old g2)

and rep_in_e vid old_expr cont_e =
  match cont_e with
  | BinOp (op, e1, e2, loc) -> 
     let e1' = rep_in_e vid old_expr e1 in
     let e2' = rep_in_e vid old_expr e2 in
     FBinop (op, e1', e2')
  | Question (c, e1, e2, loc) ->
     let c' = rep_in_e vid old_expr c in
     let e1' = rep_in_e vid old_expr e1 in
     let e2' = rep_in_e vid old_expr e2 in
     Guarded (c', e1', e2')
  | UnOp (op, e, loc) ->
     let e' = rep_in_e vid old_expr e  in
     FUnop (op, e')
  | Lval (h, o) ->
     begin
       match h with
       | Var x -> if x.vid = vid then old_expr else Container cont_e
       | _ -> Container cont_e
     end
  |_ -> Container cont_e


let replace vid old_expr new_expr =
  rep vid old_expr new_expr

let rec string_of_prefunc pf =
  match pf with
  | Empty -> "Empty"
  | Container e -> (psprint80 Cil.d_exp e)
  | FBinop (op, e1, e2) -> 
     String.concat " " [ (string_of_prefunc e1); (psprint80 Cil.d_binop op); 
                         (string_of_prefunc e2)]
  | FUnop (op, e) ->
     String.concat " " [(psprint80 Cil.d_unop op); (string_of_prefunc e)]
  | ForLoop (e0, (i, g, u), el, e) ->
     String.concat " "  ([ "Init: "^(string_of_prefunc e0)^"\nFor {"; 
                           (psprint80 Cil.d_instr i);
                           (psprint80 Cil.d_exp g); 
                           (psprint80 Cil.d_instr u);
                           "[:"]@
                            (List.map (fun e -> (psprint80 Cil.d_exp e)) el)@
                            [":]\n"; string_of_prefunc e; "}"])

  | Guarded (c, e1, e2) -> 
     "("^(string_of_prefunc c)^" ? "^(string_of_prefunc e1)^" : "^
       (string_of_prefunc e2)^")"
