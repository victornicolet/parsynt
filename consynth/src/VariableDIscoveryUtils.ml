open Utils
open SPretty
open SketchTypes
open SymbExe

module C = Cil


let is_already_computed xinfo func_expr exprs =

  IM.filter
    (fun i e ->

    )

let remove_duplicate_auxiliaries xinfo (aux_vs, aux_ef) input_func =
  let exprs = exec_once ~silent:true xinfo input_func in
  IM.fold
    (fun vid (expr, func_expr) to_rem ->
       is_already_computed xinfo func_expr exprs
        )
        aux_ef
        VS.empty
