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
  | SkCil of exp
  | SkBinop of binop * skExpr * skExpr
  | SkUnop of unop * skExpr
  | SkRec of  forIGU * skExpr
  | SkCond of skExpr * skExpr * skExpr
  | SkHole

and skStmt =  varinfo * sklet

type sketch = VS.t * skStmt list

let build_sketch (loopinfo : LF.t): sketch =
  let state_set = subset_of_list loopinfo.LF.state loopinfo.LF.allVars in
  let sketch_body = [] in
  (state_set, sketch_body)

let rec hole (expr : fexp) (vs: VS.t) =
  match expr with
  | Id i -> 
     begin
       try
         let vi = getVi i vs in
         SkVar vi
       with Not_found ->
         SkHole
     end
  | Container (e, subs) ->
     (**
        TODO : look into Cil expressions , they still contain state variables. 
     *)
     SkHole
  | Binop (op, e1, e2) ->
     let e1' = hole e1 vs in
     let e2' = hole e2 vs in
     begin
       match e1', e2' with
       | SkHole, SkHole -> SkHole
       | _, _ -> SkBinop (op, hole e1 vs, hole e2 vs)
     end
  | Unop (op, e) ->
     SkUnop (op, hole e vs)
  | Loop (igu, e) ->
     SkRec (igu, hole e vs)
  | Cond (c, e1, e2) ->
     (** 
         TODO : figure out how to generate the bookkeeping variable for conds. 
         This might require analysis of the subexpressions into the condition 
     *)
     SkHole
  
  

let pp_skexpr ppf =
  function
  | SkVar i -> fprintf ppf "%s" i.vname
  | _ -> ()
     
     
