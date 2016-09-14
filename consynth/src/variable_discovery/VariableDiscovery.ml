open Utils
open Pretty

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
