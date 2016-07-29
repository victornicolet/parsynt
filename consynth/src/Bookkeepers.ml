open Cil2Func
open Format
open Utils
open Loops

(* let insert_write_flags (letform : letin) : letin = *)
(*   let iwf_core letf = *)
(*     match letf with *)
(*     | LetCond (c, let_if, let_else, let_cont, _) -> *)

(*     | _ -> letf *)
(*   in *)
(*   transform_topdown iwf_core letform *)

let convert_igu (i, g, u) =
  let i = indexOfIGU (i, g, u) in
  (** Easy case : there is only one index *)
  (**
      Initialization of i :

  *)
