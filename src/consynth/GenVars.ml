open Utils
open FuncTypes

module Ct = CilTools

(** --------------------------------------------------------------------------*)
(*Keep track of the generated names during symbolic execution *)
type symbolic_input = (int * string * fnLVar)

let scalar_default_offset = -1
let genvars = IH.create 30

(* Add variable to the map with a vid key and offset key *)
let add_to_genvars vid offset vname subst =
  IH.add genvars vid (offset, vname, subst)

(* Find variable id with offset (for arrays or default offset for scalars)*)
let find_vid_offset vid offset =
  let symb_inp_list = IH.find_all genvars vid in
  List.find (fun (off, vn, e) -> off = offset) symb_inp_list


let exec_count = ref 0

let init () =
  IH.clear genvars;
  exec_count := 0

(* Find a variable that has the same expression. We want to avoid to create
   two different variable name for the same input (case of arrays if we access
   the same cell, we don't want to create two differnt symbols).
*)
let find_from_exp vid cexp =
  let symb_inp_list = IH.find_all genvars vid in
  let same_exp =
    List.find_all
      (fun (offset, vname, (vexp, nexp)) -> vexp = cexp)
      symb_inp_list
  in
  if List.length same_exp < 1 then
    raise Not_found
  else
    List.nth same_exp 0

(** From a sketch variable, generate a new name and a new variable
    and memorize the old expression and the new expression of the
    variable.
    @param v the variable expression, a SkLVar
    @return the offset of the varaible corresponding to the number of
    expansions realised, the new name of the variable and a pair
    representing the substituion of the expression in the code by
    the new expression of the variable.
*)

let rec gen_var v =
  try
    let host_vi = check_option (vi_of v) in
    try
      find_from_exp host_vi.vid v
    with Not_found ->
      let vname = host_vi.vname in
      let new_vi = {host_vi with vname=host_vi.vname^(string_of_int !exec_count)}in
      let new_v = FnVariable new_vi in
      let offset =
        match v with
        | FnVariable _ -> scalar_default_offset
        | FnArray _ -> !exec_count
      in
      add_to_genvars host_vi.vid offset vname (v, new_v);
      (offset, new_vi.vname, (v,new_v))
  with Failure s ->
    raise
      (Failure
         (Format.fprintf Format.str_formatter
            "%s@.Variable:%a@.Initial message: %s@."
            "Failed to find host variable in gen_var"
            FPretty.pp_fnlvar v
            s;
          Format.flush_str_formatter ()))

(* Filter out the new variable part in the variable generation output *)
let gen_expr v =
  let _, _, (_, ev) = gen_var v in FnVar ev

let declared_vars () =
  IH.fold
    (fun i (offset, vname, (v, new_v)) vs ->
       let vi = vi_of new_v in
       if is_some vi then VarSet.add {(check_option vi) with vname = vname} vs
       else vs)
    genvars VarSet.empty
