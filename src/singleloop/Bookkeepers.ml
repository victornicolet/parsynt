open Format
open Utils
open Cil
open Findloops
open VariableAnalysis

(* let insert_write_flags (letform : letin) : letin = *)
(*   let iwf_core letf = *)
(*     match letf with *)
(*     | LetCond (c, let_if, let_else, let_cont, _) -> *)

(*     | _ -> letf *)
(*   in *)
(*   transform_topdown iwf_core letform *)
type igu = varinfo * Cil.exp * Cil.exp * Cil.exp

let convert_igu (i, g, u) reaching_consts =
  let indexes = index_of_igu (i, g, u) in
  (** Easy case : there is only one index *)
  if VS.cardinal indexes = 1
  then
    let index = VS.max_elt indexes in
    let init_val =
      try
        (IM.find index.vid reaching_consts)
      with Not_found ->
        (match i with
        | Set (vi, Const c, t) -> c
        | _ -> failwith "Unrecognized statement in init loop")
    in
    let increment =
      match u with
      | Set ((h,o), BinOp(op, e1, e2, t), t) ->
         (match e1, e2 with
         | Lval (h', _), e | e, Lval (h', _) ->
            (let vi', _ = analyze_host h' in
             let vi , _ = analyze_host h in
             if vi = vi' then
               e
             else
               failwith "TODO")
         | _, _ -> )
      | Set (vi, UnOp(op, e, t), t) ->
         ()
    in
    (index, init_val, g, increment)

  else ()
  (**
      Initialization of i :

  *)
