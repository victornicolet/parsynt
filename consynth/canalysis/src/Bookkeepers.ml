open Cil2Func
open Format
open Utils

let get_uses i = IH.find i uses


let insert_write_flags (letform : letin) : letin =
  let iwf_core letf =
    match letf with
    | LetCond (c, let_if, let_else, let_cont, _) ->

    | _ -> letf
  in
  transform_topdown iwf_core letform
