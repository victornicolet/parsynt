open Utils
open Cil
open Format
open PpHelper
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
  | Container of Cil.exp * substitutions
  | Binop of Cil.binop * fexp * fexp
  | Unop of Cil.unop * fexp
  (**
      A loop enclosing an assignment is reduced to the IGU,
      the subscripts if it is an array and the right-hand side
      expression in the assignment.
      The subscript expression list is empty if it is a scalar.
  *)
  (** init, igu, subscripts, expression *)
  | Loop of Loops.forIGU * fexp
  (* An expression guarded by an if *)
  | Cond of fexp * fexp * fexp

and substitutions = (int * fexp) list

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
    for a given variable v and statevariables x
*)
let rec build  g (expr : Cil.exp) (x : Cil.varinfo)
    (statevars : int list)=
  match g with
  | GEmpty -> Container (expr, [])
  | GCond (e, g') -> Cond (Container (e, []),
                              (build g' expr x statevars),
                              Id x.vid)
  | GFor (igu, g') ->
     Loop (igu, build g' expr x statevars)


let rec rep vid old ne =
  match ne with
  | Id vid -> ne
  | Container (e, li) -> Container (e, li@[(vid, ne)])
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
       | Var x -> if x.vid = vid then old_expr else Container (cont_e, [])
       | _ -> Container (cont_e, [])
     end
  |_ -> Container (cont_e, [])

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
       | Container (e, []) when e = v2e v -> Exp newe
       | Id vid when v.vid = vid -> Exp newe
       | Id vid -> Let(v.vid, newe, Exp (Id vid))
       | _ -> Let(v.vid, eold, Exp(newe))
     end

(**
   Put the new lambda at the end of the old lambda, and put last
   expression in the old lambda in a let in using the vid provided
   as argument.
*)
let rec letin_lam (vid : int) (old : lambda) (nlam : lambda) =
  match old with
  | Exp e -> Let(vid, e, nlam)
  | Let (x, e, l) -> Let (x, e, letin_lam vid l nlam)

let let_in_func v old newe =
  match newe with
  | Exp e ->
     begin
       match old with
       | Empty vi -> Func (vi, Let(v.vid, e, Exp (Id vi.vid)))
       | Func (vi, lam) -> Func (vi, letin v lam e)
     end
  | Let (vi0, expr, lam) ->
     begin
       match old with
       | Empty vi -> Func (vi, newe)
       | Func (vi, lam) -> Func (vi, letin_lam vi.vid lam newe)
     end

let rec reduce_v (vid: int) (lam : lambda) (state : fexp IH.t) =
  let step main_vid e =
    let ne = IH.fold
      (fun i v eacc ->
        replace i eacc v)
      state e in
    IH.replace state main_vid ne
  in
  match lam with
  | Exp e -> step vid e
  | Let (xid, fexpr, lam') ->
     step xid fexpr;
    reduce_v vid lam' state




let reduce (func : preFunc) : fexp =
  match func with
  | Empty vi -> Id vi.vid
  | Func (vi, lam) ->
     let hm = IH.create 10 in
     reduce_v vi.vid lam hm;
     IH.find hm vi.vid



let rec pr_prefunc ppf =
  function
  | Empty vi ->
     fprintf ppf "@[empty %s@]" vi.vname

  | Func (vi, lam) ->
     fprintf ppf
       "@[%s =@. %a @]"
       vi.vname
       pr_lam lam

and pr_lam ppf =
  function
  | Exp e ->
     pr_fexp ppf e

  | Let (i, x, e) ->
     fprintf ppf
       "@[%sLet%s %s = @[<2>%a@] @;%sin%s@;@[%a@] @]"
       (color "red") (color "")
       (string_of_int i)
       pr_fexp x
       (color "red") (color "")
       pr_lam e

and pr_fexp ppf =
  function
  | Id i ->
     fprintf ppf "(%i)" i

  | Container (e, []) ->
     fprintf ppf
       "@[\"%s\"@]"
       (psprint80 Cil.dn_exp e)

  | Container (e, l) ->
     fprintf ppf
       "@[\"%s\"[%s]@]"
       (psprint80 Cil.dn_exp e)
       (String.concat
          " "
          (List.map
          (fun (i, fexpr) ->
            (sprintf "%i -> %s" i "xx"))
          l
          ))

  | Binop (op, e1, e2) ->
     fprintf ppf
       "@[%a %s @;%a@]"
       pr_fexp e1
       (psprint80 Cil.d_binop op)
       pr_fexp e2

  | Unop (op, e) ->
     fprintf ppf
       "%s %a"
       (psprint80 Cil.d_unop op)
       pr_fexp e

  | Loop ((i, g, u), e) ->
     fprintf ppf
       "for (%s; %s; %s) {@; @[%a@]} end@;"
       (psprint80 Cil.dn_instr i)
       (psprint80 Cil.dn_exp g)
       (psprint80 Cil.dn_instr u)
       pr_fexp e

  | Cond (c, e1, e2) ->
     fprintf ppf
       "(@[%a@] ? @; @[%a@] : @[%a@])@;"
       pr_fexp c
       pr_fexp e1
       pr_fexp e2

let string_of_fexp fexp =
  pr_fexp str_formatter fexp; flush_str_formatter ()
let string_of_lambda lam =
  pr_lam str_formatter lam; flush_str_formatter ()
let string_of_prefunc pref =
  pr_prefunc str_formatter pref; flush_str_formatter ()

let eprint_fexp = pr_fexp err_formatter
let eprint_lambda = pr_lam err_formatter
let eprint_prefunc = pr_prefunc err_formatter

let print_fexp = pr_fexp std_formatter
let print_lambda = pr_lam std_formatter
let print_prefunc = pr_prefunc std_formatter

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
  | Id i -> VSOps.subset_of_list [i] stv
  | Container (ec, l) -> VSOps.sove ec
  | Binop (op, e1, e2) -> VS.union (vs_of_fexp stv e1) (vs_of_fexp stv e2)
  | Unop (op, e1) -> vs_of_fexp stv e1
  | Loop (_, e) -> (vs_of_fexp stv e)
  | Cond (e', e1, e2) ->
     List.fold_left
       VS.union       VS.empty
       (List.map (vs_of_fexp stv) [e'; e1; e2])
