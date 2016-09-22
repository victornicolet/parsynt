open Cil
open Utils
open Pretty
open ExpressionReduction
open SymbExe

module Ty = SketchTypes


(**
   Entry point : check that the function is a candidate for
    function discovery.
*)

let rec check_wf (input_function : Ty.sklet) (stv : VS.t) : Ty.sklet =
  match input_function with
  | Ty.SkLetExpr assignments ->
    input_function
  | Ty.SkLetIn (assignments, skletexpr) ->
    failwith "TODO : body with inner dependencies"

and check_wf_assignments (assignments : (Ty.skLVar * Ty.skExpr) list)
    (state : VS.t)=
  try
    List.iter
      (fun (v, e) ->
         if accepted_expression e
         then ()
         else raise (Failure "bad assgn")) assignments;
    true
  with Failure s -> false

and accepted_expression e =
  match e with
  | Ty.SkVar _
  | Ty.SkConst _ -> true
  | Ty.SkQuestion _ -> true
  | Ty.SkUnop (_, e') -> accepted_expression e'
  | Ty.SkBinop (_, e', e'') ->
    (accepted_expression e') && (accepted_expression e'')
  | _ -> false


(** Rank the state variable according to sequential order assignment and then
    the number of incoming edges in the use-def graph.
*)
let merge_union vid ao bo =
  match ao, bo with
  | Some a, Some b -> Some (VS.union a b)
  | Some a, None -> Some a
  | _ , Some b -> Some b
  | _ ,_ -> None

let update_map map vi vi_used =
  try
    IM.add vi.vid (VS.union vi_used (IM.find vi.vid map)) map
  with Not_found ->
    IM.add vi.vid vi_used map

let uses stv input_func =
  let uses_map = VS.fold (fun vi m -> IM.add vi.vid 0 m) stv IM.empty in
  let rec aux_used_stvs stv inpt map =
    match inpt with
    | Ty.SkLetIn (velist, letin) ->
      let new_uses = List.fold_left used_in_assignment map velist in
      let letin_uses = aux_used_stvs stv inpt IM.empty in
      IM.merge merge_union new_uses letin_uses
    | Ty.SkLetExpr velist -> List.fold_left used_in_assignment map velist

  and used_in_assignment map (v, expr) =
    let vi = check_option (Ty.vi_of v) in
    let f_expr = Ty.rec_expr
        VS.union (* Join *)
        VS.empty (* Leaf *)
        (fun c -> VS.empty) (* Handle constants *)
        (fun v ->
           VS.inter
             (VS.singleton (check_option (Ty.vi_of v))) stv) (* Variables *)
    in
    update_map map vi (f_expr expr)

let discover stv input_func (i,g,u) = ()
