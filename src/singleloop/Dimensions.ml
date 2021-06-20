(**
   This file is part of Parsynt.

    Parsynt is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
*)

open Fn
open FnPretty
open Format
open Beta
open Utils

let iterations_limit = Config.get_conf_int "loop_finite_limit"

let inner_iterations_limit = Config.get_conf_int "inner_loop_finite_limit"

let mat_w = ref 0

let mat_h = ref 0

let set_default () =
  mat_w := inner_iterations_limit;
  mat_h := iterations_limit

let set_large_square () =
  mat_w := iterations_limit;
  mat_h := iterations_limit

let set_small_square () =
  mat_w := inner_iterations_limit;
  mat_h := inner_iterations_limit

let reset_matdims () = set_default ()

let width () = !mat_w

let height () = !mat_h

let dims () = (!mat_h, !mat_w)

let bounds (fixed : bool) (sketch : prob_rep) : fnExpr * fnExpr =
  let ist, ien = get_bounds sketch in
  if fixed then (FnConst (CInt 0), FnConst (CInt (width ()))) else (mkVarExpr ist, mkVarExpr ien)

(* If possible, link indexes to intervals and guess arrary dimensions.
   Experimental : later, use solver.
*)

type e_interval = fnExpr * fnExpr

let pp_interval fmt iv =
  Format.fprintf fmt "[%a; %a]" FnPretty.pp_fnexpr (fst iv) FnPretty.pp_fnexpr (snd iv)

(* Managin n,m .. *)
let _SYMBEX_FINITE_ = Config.get_conf_int "symbolic_execution_finitization"

type boundinfo = { synthesis : int; symbex : int }

let _bndmap : boundinfo IH.t = IH.create 10

let pop_flag = ref false

let pop_bnd () =
  if !pop_flag then inner_iterations_limit
  else (
    pop_flag := true;
    iterations_limit)

let add_bound (n : fnV) : unit =
  if IH.mem _bndmap n.vid then () else IH.add _bndmap n.vid { synthesis = pop_bnd (); symbex = 5 }

(* Maps index to the interval it belongs to in the original loops. *)
let _index_intervals : e_interval IH.t = IH.create 5

(* Maps array variables to dimensions. *)
let _array_dimensions : e_interval list IH.t = IH.create 5

let register_index_dims index (i0, iN) =
  (match (i0, iN) with
  | FnConst _, FnVar (FnVariable n) | FnVar (FnVariable n), FnConst _ -> add_bound n
  | _ -> ());
  IH.add _index_intervals index.vid (i0, iN)

let update_index_interval (i : fnV) interval =
  try
    let prev_interval = IH.find _index_intervals i.vid in
    if prev_interval = interval then true else false
  with Not_found ->
    IH.add _index_intervals i.vid interval;
    true

let reg_array_subscript (a : fnExpr) (i : fnExpr) : unit =
  let add_dim a dims = IH.add _array_dimensions a.vid dims in
  let avar, aoffset =
    match a with
    | FnVar (FnVariable a') -> (a', [])
    | FnVar (FnArray (FnVariable a', i')) -> (a', [ i' ])
    | FnVar (FnArray (FnArray (FnVariable a', i'), j')) -> (a', [ i'; j' ])
    | _ -> failhere __FILE__ "reg_array_subscript" "Too many dimensions."
  in
  let get_offset_interval e =
    let interval i = IH.find _index_intervals i.vid in
    match e with
    | FnBinop (Minus, FnVar (FnVariable ii), c) ->
        let i0, iN = interval ii in
        (FnBinop (Minus, i0, c), FnBinop (Minus, iN, c))
    | FnBinop (Plus, FnVar (FnVariable ii), c) ->
        let i0, iN = interval ii in
        (FnBinop (Plus, i0, c), FnBinop (Plus, iN, c))
    | FnVar (FnVariable ii) -> interval ii
    | FnConst (CInt _) -> (e, e)
    | _ ->
        Format.printf "%a" FnPretty.pp_fnexpr e;
        failhere __FILE__ "get_offset_interval" "Index subscript not supported."
  in
  add_dim avar (List.map get_offset_interval (aoffset @ [ i ]))

let dimensionalize ((init, grd, upd) : fnExpr * fnExpr * fnExpr) =
  let i1 = used_in_fnexpr init in
  let i2 = used_in_fnexpr grd in
  let i3 = used_in_fnexpr upd in
  let ii =
    if VarSet.is_empty i1 then VarSet.inter i2 i3
    else if VarSet.is_empty i2 then VarSet.inter i1 i3
    else VarSet.inter i1 (VarSet.inter i2 i3)
  in
  if VarSet.is_empty ii || VarSet.cardinal ii > 1 then
    failwith "Dimensions : wrong number of indexes.";
  let index = VarSet.max_elt ii in
  let i_interval =
    match (init, grd) with
    | FnConst _, FnBinop (Lt, FnVar (FnVariable i'), imax)
    | FnConst _, FnBinop (Gt, imax, FnVar (FnVariable i'))
      when i' = index ->
        (init, imax)
    | FnConst _, FnBinop (Ge, imax, FnVar (FnVariable i'))
    | FnConst _, FnBinop (Le, FnVar (FnVariable i'), imax)
      when i' = index ->
        (init, FnUnop (Add1, imax))
    | FnConst _, FnBinop (Gt, FnVar (FnVariable i'), imax)
    | FnConst _, FnBinop (Lt, imax, FnVar (FnVariable i'))
      when i' = index ->
        (imax, init)
    | FnConst _, FnBinop (Le, imax, FnVar (FnVariable i'))
    | FnConst _, FnBinop (Ge, FnVar (FnVariable i'), imax)
      when i' = index ->
        (FnUnop (Add1, imax), init)
    | _ -> failwith "Dimensions: index/guard not defining an interval?"
  in

  if update_index_interval index i_interval then ()
  else failhere __FILE__ "dimensionalize" "Conflict for an index."

let dimensionalize_body body =
  rec_expr2
    {
      case = (fun e -> match e with FnArraySet _ -> true | _ -> false);
      on_case =
        (fun f e ->
          match e with
          | FnArraySet (a, i, e) ->
              reg_array_subscript a i;
              f e
          | _ -> ());
      on_var =
        (fun v ->
          match v with FnVariable _ -> () | FnArray (a, i) -> reg_array_subscript (FnVar a) i);
      on_const = (fun _ -> ());
      init = ();
      join = (fun _ _ -> ());
    }
    body

let rec register_dimensions_igu (pb : prob_rep) =
  List.iter register_dimensions_igu pb.inner_functions;
  dimensionalize (snd pb.func_igu)

let rec register_dimensions_arrays (pb : prob_rep) =
  List.iter register_dimensions_arrays pb.inner_functions;
  dimensionalize_body pb.main_loop_body

let get_index_dims index = IH.find _index_intervals index.vid

let get_array_dims array = IH.find _array_dimensions array.vid

let get_concrete v = try Some (IH.find _bndmap v.vid) with Not_found -> None

let concretize (e : fnExpr) =
  let g v =
    match v with
    | FnVar (FnVariable var) -> (
        match get_concrete var with Some c -> FnConst (CInt c.symbex) | None -> v)
    | _ -> v
  in
  transform_expr2
    {
      case = (fun e -> match e with FnVar _ -> true | _ -> false);
      on_case = (fun _ e -> g e);
      on_var = identity;
      on_const = identity;
    }
    e

let print_status () =
  printf "Index intervals:@.";
  IH.iter
    (fun k interval ->
      printf "@[<v 4>\t%i : %s --> [%a; %a]@]@." k
        (try (find_var_id k).vname with Not_found -> "??")
        pp_fnexpr (fst interval) pp_fnexpr (snd interval))
    _index_intervals;
  printf "Array bounds:@.";
  IH.iter
    (fun k intervals ->
      printf "@[<v 4>\t%i : %s --> %a@]@." k
        (try (find_var_id k).vname with Not_found -> "??")
        Fmt.(
          list ~sep:sp (fun fmt interval ->
              fprintf fmt "[%a; %a]" pp_fnexpr (fst interval) pp_fnexpr (snd interval)))
        intervals)
    _array_dimensions
