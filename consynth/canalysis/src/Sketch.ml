open Utils
open Cil
open Loops
open Printf
open Format
open Prefunc

module VS = VS
module LF = Loops2ssa.Floop

type sklet =
  | SkLetExpr of skExpr
  | SkLetIn of int * skExpr * sklet

and skExpr =
  | SkVar of varinfo
  | SkArray of varinfo * (skExpr list)
  | SkCil of exp (** If expression doesn't contain state variables *)
  | SkBinop of binop * skExpr * skExpr
  | SkUnop of unop * skExpr
  | SkRec of  forIGU * skExpr
  | SkCond of skExpr * skExpr * skExpr
  | SkHole
(** Simple translation of Cil exp needed to nest
    sub-expressions with state variables *)
  | SkConst of constant
  | SkLval of lval
  | SkSizeof of typ
  | SkSizeofE of skExpr
  | SkSizeofStr of string
  | SkAlignof of typ
  | SkAlignofE of skExpr
  | SkCastE of typ * skExpr
  | SkAddrof of lval
  | SkAddrofLabel of stmt ref
  | SkStartOf of lval

and skStmt =  varinfo * sklet

type sketch = VS.t * skStmt list

let build_sketch (loopinfo : LF.t): sketch =
  let state_set = VSOps.subset_of_list loopinfo.LF.state loopinfo.LF.allVars in
  let sketch_body = [] in
  (state_set, sketch_body)

let hole_or_exp constr e =
  match e with
  | SkHole -> SkHole
  | _ -> constr e

let hole_or_exp2 constr e1 e2 =
  match e1, e2 with
  | SkHole, SkHole -> SkHole
  | _, _ -> constr e1 e2

let rec hole (vs: VS.t) =
 function
  | Id i ->
     begin
       try
         let vi = VSOps.getVi i vs in
         SkVar vi
       with Not_found ->
         SkHole
     end
  | Container (e, subs) ->
     let usv = VS.inter (VSOps.sove e) vs in
     if VS.cardinal usv > 0 then
       hole_cils vs e
     else SkHole

  | Binop (op, e1, e2) ->
     let e1' = hole vs e1 in
     let e2' = hole vs e2 in
     begin
       match e1', e2' with
       | SkHole, SkHole -> SkHole
       | _, _ -> SkBinop (op, hole vs e1, hole vs e2)
     end
  | Unop (op, e) ->
     SkUnop (op, hole vs e)
  | Loop (igu, e) ->
     SkRec (igu, hole vs e)
  | Cond (c, e1, e2) ->
     (**
         TODO : figure out how to generate the bookkeeping variable for conds.
         This might require analysis of the subexpressions into the condition
     *)
     SkHole

and hole_cils (vs : VS.t) =
  function
  | Const c -> SkHole

  | Lval v ->
     if VSOps.hasLval v vs then
       SkLval v (** TODO : better matching lvalue -> SkVar or Skvar + offset *)
     else
       SkHole

  | SizeOf t->
     SkSizeof t

  | SizeOfE e ->
     hole_or_exp (fun x -> SkSizeofE x) (hole_cils vs e)

  | SizeOfStr s ->
     SkSizeofStr s

  | AlignOf t ->
     SkAlignof t

  | AlignOfE e ->
     hole_or_exp (fun x -> SkAlignofE x) (hole_cils vs e)

  | AddrOf lv ->
     SkAddrof lv

  | AddrOfLabel stm_ref ->
     SkAddrofLabel stm_ref

  | UnOp (op, e1, t) ->
     hole_or_exp (fun x -> SkUnop (op,x)) (hole_cils vs e1)

  | BinOp (op, e1, e2, t) ->
     hole_or_exp2
       (fun x1 x2 -> SkBinop (op, x1, x2))
       (hole_cils vs e1)
       (hole_cils vs e2)

  | Question (c, e1, e2, t) ->
     let c' = hole_cils vs c in
     (** TODO : do something more specific with the question *)
     hole_or_exp2
       (fun x1 x2 -> SkCond (c', x1, x2))
       (hole_cils vs e1)
       (hole_cils vs e2)
  | CastE (t, e) ->
     SkCastE (t, hole_cils vs e)
  | StartOf lv ->
     SkStartOf lv



let pp_skexpr ppf =
  function
  | SkVar i -> fprintf ppf "%s" i.vname
  | _ -> ()
