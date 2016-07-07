open Utils
open Cil
open Format
open Prefunc
open Core.Std
open Utils
open SketchTypes
open SPretty
open PpHelper

module VS = VS
module LF = Loops2ssa.Floop
module SM = Map.Make (String)


let debug = ref false;;

(**
   The main entry point of the file is build_sketch :
   build a sketch from the Floop (vector of functions
   for each state variable representing the ody of the
   loop).
*)
(**
    Replacing old expressions by sketch epxressions, and putting holes
    in some places.
*)

let hole_or_exp constr e =
  match e with
  | SkHoleL -> SkHoleL
  | SkHoleR -> SkHoleR
  | _ -> constr e

let hole_or_exp2 constr e1 e2 =
  match e1, e2 with
  | SkHoleL, SkHoleL -> SkHoleL
  | SkHoleR, SkHoleR -> SkHoleR
  | _, _ -> constr e1 e2

let rec hole (vs: VS.t) =
 function
  | Id i ->
     begin
       try
         let vi = VSOps.getVi i vs in
         SkVar vi
       with Not_found ->
         SkHoleR
     end
  | Container (e, subs) ->
     let usv = VS.inter (VSOps.sove e) vs in
     if VS.cardinal usv > 0 then
       hole_cils vs e
     else SkHoleR

  | Binop (op, e1, e2) ->
     let e1' = hole vs e1 in
     let e2' = hole vs e2 in
     begin
       match e1', e2' with
       | SkHoleR, SkHoleR -> SkHoleR
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
     SkHoleR

and hole_cils (vs : VS.t) =
  function
  | Const c -> SkHoleR

  | Lval v ->
     if VSOps.hasLval v vs then
       SkLval v (** TODO : better matching lvalue -> SkVar or Skvar + offset *)
     else
       SkHoleR

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

and hole_lam (vs: VS.t) =
  function
  | Prefunc.Exp e -> SkLetExpr (hole vs e)
  | Prefunc.Let (i, e, l) ->
     try
       let vi = VSOps.getVi i vs in
       SkLetIn (vi, hole vs e, hole_lam vs l)
     with Not_found ->
       if !debug then
         printerr
           (Format.sprintf "Didn't find variable id  %s in %s"
              (string_of_int i) (VSOps.spvs vs));
       failwith "Not_found : a variable in let is not in the state"

and hole_prefunc (vs : VS.t) =
  function
  | Empty x -> (x, SkLetExpr (SkVar x))
  | Func (x,l) -> (x, hole_lam vs l)

(*** MAIN ENTRY POINT ***)

let build_sketch (loopinfo : LF.t): sketch =
  let state_set = VSOps.subset_of_list loopinfo.LF.state loopinfo.LF.allVars in
  let sketch_body =
    List.map (IH.tolist loopinfo.LF.body)
      ~f:(fun (i,b) -> hole_prefunc state_set b)
  in
  (state_set, sketch_body)

(******************************************************************************)

(**
    Compile the Rosette sketch.
    Rosette is using Racket, which is based on s-expresssions
    so we will be using the Sexplb library to convert types
    directly to s-expressions
*)


(** A symbolic definition defines a list of values of a given type,
    the second string in the type corresponds *)

(** Type for building the defintions list *)
type defsRec =
  { ints : string list ;
    reals : string list ;
    bools : string list ;
    vecs : (string * string) list }

(**
     Type suitable for printing s-expressions that will be used
     as Racket macros.
*)
type symbDef =
  | Integers of string list
  | Reals of string list
  | Booleans of string list
  | RoArray of string * string list
[@@deriving sexp]

let add_to_reals s defs =
  { defs with reals = s::defs.reals }

let add_to_booleans s defs =
  { defs with bools = s::defs.bools }

let add_to_integers s defs =
  { defs with ints = s::defs.ints }

let add_to_vectors ty s defs =
  let osty = ostring_of_baseSymbolicType ty in
  match osty with
  | Some sty -> { defs with vecs = (s, sty)::defs.vecs }
  | None ->
     eprintf "add_to_vectors : vector of type too complex";
    defs

let adding_function vtype =
  let symb_type = symb_type_of_ciltyp vtype in
  match symb_type with
  | Unit -> identity2
  | Integer -> add_to_integers
  | Real -> add_to_reals
  | Boolean -> add_to_booleans
  | Vector (ty, _) -> add_to_vectors ty
  | _ ->  identity2

let add_varinfo vi defs  =
  (adding_function vi.vtype) vi.vname defs

let defsRec_to_symbDefs defs_rec
    : (symbDef * symbDef * symbDef * (symbDef list) ) =
  let ro_arrays_map =
    List.fold_left
      defs_rec.vecs
      ~init:SM.empty
      ~f:(fun tmap (vname, sty) ->
        SM.update tmap sty
          (function
          | Some l -> vname::l
          | None -> [vname] ))
  in
  let ro_arrays = SM.to_alist ro_arrays_map in
  let roArrays = List.map  ro_arrays ~f:(fun (k,v) -> RoArray (k, v))
  in
  (
    Integers defs_rec.ints,
    Reals defs_rec.reals,
    Booleans defs_rec.bools,
    roArrays
  )


(** Sketch -> Rosette sketch *)

let strings_of_symbdefs1 symbdef =
  let sexpr = sexp_of_symbDef symbdef in
  string_of_sexp sexpr


let symbolic_definitions_of vars = []

let join_sketch_of sketch = []

let loop_body_of sketch = []

let assertions_of sketch = []

let synthesis_statement_of sketch = []

let rosette_sketch_of sketch =
  let symbolic_definitions = symbolic_definitions_of sketch in
  let join_sketch = join_sketch_of sketch in
  let loop_body = loop_body_of sketch in
  let additional_assertions = assertions_of sketch in
  let main_pb = synthesis_statement_of sketch in
  Stream.of_list     (symbolic_definitions@
                        join_sketch@
                        loop_body@
                        additional_assertions@
                        main_pb)
