open Utils
open Cil

module VS = VS

(** ------------------------------------------------------------------*)
(** Type for intermediary representation of the loop body *)
(** The loop body is a Inthash from the state variable ids
    to an expression of type preFunc *)
(** Short functional representation *)
type preFunc =
  | Empty of varinfo
  | Func of varinfo * lambda

and lambda = 
  | Exp of fexp
  | Let of int * fexp * lambda
  (** A cil expression *)
and fexp =
  (* *)
  | Id of int
  | Container of Cil.exp
  | Binop of Cil.binop * fexp * fexp
  | Unop of Cil.unop * fexp
  (**
      A loop enclosing an assignment is reduced to the IGU,
      the subscripts if is is an array and the right-hand side
      expression in the assignment.
      The subscript expression list is empty if it is a scalar.
  *)
  (** init, igu, subscripts, expression *)
  | Loop of Loops.forIGU * fexp
  (* An expression guarded by an if *)
  | Cond of fexp * fexp * fexp

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

(** 
    Build the expression that will be put in the let/in form,
    for a given varaible v and statevariables x
*)
let rec build  g (expr : Cil.exp) (x : Cil.varinfo) 
    (statevars : int list)=
  match g with
  | GEmpty -> Container expr
  | GCond (e, g') -> Cond (Container e,
                              (build g' expr x statevars),
                              Id x.vid)
  | GFor (igu, g') ->
     Loop (igu, build g' expr x statevars)


let rec rep vid old ne =
  match ne with
  | Id vid -> Id vid
  | Container e -> (rep_in_e vid old e)
  | Binop (op, e1, e2) -> Binop (op, rep vid old e1, rep vid old e2)
  | Unop (op, e) -> Unop (op, rep vid old e)
  | Loop (igu, g) -> Loop (igu, rep vid old g)
  | Cond (e, g1, g2) -> Cond (e, rep vid old g1,
                                    rep vid old g2)

and rep_in_e vid old_expr cont_e =
  match cont_e with
  | BinOp (op, e1, e2, loc) ->
     let e1' = rep_in_e vid old_expr e1 in
     let e2' = rep_in_e vid old_expr e2 in
     Binop (op, e1', e2')
  | Question (c, e1, e2, loc) ->
     let c' = rep_in_e vid old_expr c in
     let e1' = rep_in_e vid old_expr e1 in
     let e2' = rep_in_e vid old_expr e2 in
     Cond (c', e1', e2')
  | UnOp (op, e, loc) ->
     let e' = rep_in_e vid old_expr e  in
     Unop (op, e')
  | Lval (h, o) ->
     begin
       match h with
       | Var x -> if x.vid = vid then old_expr else Container cont_e
       | _ -> Container cont_e
     end
  |_ -> Container cont_e

(** Replace vid by the old expression in new expr *)
let replace vid old_expr new_expr =
  rep vid old_expr new_expr

(** Adds a new let v = newe in .. 
    at the end of the old lambda *)
let rec letin v old newe =
  match old with
  | Let (i, x , olde) -> letin v olde newe
  | Exp eold -> 
     begin
       match eold with 
       | Container e when e = v2e v -> Exp newe
       | Id vid when v.vid = vid -> Exp newe
       | Id vid -> Let(v.vid, newe, Exp (Id vid))
       | _ -> Let(v.vid, eold, Exp(newe))
     end

let let_in_func v old newe =
  match old with
  | Empty vi -> Func (vi, Let(v.vid, newe, Exp (Id vi.vid)))
  | Func (vi, lam) -> Func (vi, letin v lam newe)

 

let rec string_of_prefunc pf =
  match pf with
  | Empty vi -> "Empty "^vi.vname
  | Func (vi, lam) -> vi.vname^" = "^(string_of_lambda lam)

and string_of_lambda lam =
  match lam with
  | Exp e -> string_of_fexp e
  | Let (i, x, e) -> "Let "^(string_of_int i)^" = "^
     (string_of_fexp x)^"\nIn "^(string_of_lambda e)

and string_of_fexp fexp =
  match fexp with 
  | Id i -> Printf.sprintf "(%i)" i
  | Container e -> "\""^(psprint80 Cil.d_exp e)^"\""
  | Binop (op, e1, e2) ->
     String.concat " " [ (string_of_fexp e1); (psprint80 Cil.d_binop op);
                         (string_of_fexp e2)]
  | Unop (op, e) ->
     String.concat " " [(psprint80 Cil.d_unop op); (string_of_fexp e)]
  | Loop ((i, g, u), e) ->
     String.concat " "  ([ "\nFor (";
                           (psprint80 Cil.dn_instr i);
                           (psprint80 Cil.dn_exp g);
                           (psprint80 Cil.dn_instr u)]@
                            [")\n"; string_of_fexp e; "EndFor"])

  | Cond (c, e1, e2) ->
     "("^(string_of_fexp c)^" ? "^(string_of_fexp e1)^" : "^
       (string_of_fexp e2)^")"

(** Variable set used in a function *)
let rec vs_of_prefunc stv pf =
  match pf with 
  | Empty vi -> VS.empty
  | Func (vi, lam) -> VS.union (VS.singleton vi) (vs_of_lam stv lam)

and vs_of_lam stv lam =
  match lam with 
  | Exp e -> vs_of_fexp stv e
  | Let (i, e, lam') -> VS.union (vs_of_fexp stv e) (vs_of_lam stv lam)

and vs_of_fexp stv e =
  match e with 
  | Id i -> subset_of_list [i] stv
  | Container ec -> sove ec
  | Binop (op, e1, e2) -> VS.union (vs_of_fexp stv e1) (vs_of_fexp stv e2)
  | Unop (op, e1) -> vs_of_fexp stv e1
  | Loop (_, e) -> (vs_of_fexp stv e)
  | Cond (e', e1, e2) -> 
     List.fold_left 
       VS.union       VS.empty
       (List.map (vs_of_fexp stv) [e'; e1; e2])
