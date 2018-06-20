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

open Beta
open Format
open FnPretty
open Fn
open SymbExe
open Utils

let verbose = ref false

(** Rank the state variable according to sequential order assignment and then
    the number of incoming edges in the use-def graph.
*)
let merge_union vid ao bo =
  match ao, bo with
  | Some a, Some b -> Some (VarSet.union a b)
  | Some a, None -> Some a
  | _ , Some b -> Some b
  | _ ,_ -> None

let update_map map vi vi_used =
  if IM.mem vi.vid map then
    IM.add vi.vid (VarSet.union vi_used (IM.find vi.vid map)) map
  else
    IM.add vi.vid vi_used map

let uses stv input_func =
  let f_expr = rec_expr
      VarSet.union (* Join *)
      VarSet.empty (* Leaf *)
      (fun e -> false) (* No special cases *)
      (fun f e -> VarSet.empty) (* Never used*)
      (fun c -> VarSet.empty) (* Handle constants *)
      (fun v ->
         VarSet.inter
           (VarSet.singleton (var_of_fnvar v)) stv) (* Variables *)
  in
  let rec aux_used_stvs stv inpt map =
    match inpt with
    | FnLetIn (velist, letin) ->
      let new_uses = List.fold_left used_in_assignment map velist in
      let letin_uses = aux_used_stvs stv letin IM.empty in
      IM.merge merge_union new_uses letin_uses

    | FnRecord (vs, emap) ->
      IM.fold
        (fun i e map' ->
           used_in_assignment map' (FnVariable(VarSet.find_by_id vs i), e))
        emap
        map

    | _ -> failhere __FILE__ "uses"
             "Bad toplevel expr form, recursion should not have reached this."
  and used_in_assignment map (v, expr) =
    let var = var_of_fnvar v in
    if VarSet.mem var stv then update_map map var (f_expr expr) else map
  in
  aux_used_stvs stv input_func IM.empty


let rec collect_dependencies (ctx : context) (func : fnExpr) : VarSet.t IM.t =
  let lbody =
    transform_expr2
      { case = (fun e -> match e with FnArraySet _ -> true | _ -> false);
        on_case =
          (fun f e ->
             match e with
             | FnArraySet (a, i, ae) -> FnArraySet (a, FnConst(CInt 0), f ae)
             | _ -> e);
        on_var =
          (fun v ->
             match v with
             | FnVariable var -> v
             | FnArray (v, e) -> FnArray(v, FnConst(CInt 0)));
        on_const = identity
      } func
  in
  if !verbose then
    printf "[INFO]@[<v 4>Collect dependencies on function:@;%a@]@." pp_fnexpr lbody;

  try
    let final_exprs, _  =
      unfold
        { context = ctx;
          state_exprs = SymbExe.create_symbol_map ctx.state_vars;
          intermediate_states = IM.empty;
          index_exprs = IM.map (fun x -> FnConst(CInt 0))
              (IM.of_alist (VarSet.bindings ctx.index_vars));
          inputs = ES.empty
        }
        lbody
    in
    IM.map (fun e -> used_in_fnexpr e) final_exprs
  with SymbExeError (s, e) ->
    if !verbose then
      begin
        printf "[ERROR] Symbolic execution error while colecting dependencies.@.";
        printf "        Reverting to simpler version of dependency collection."
      end;
    uses ctx.state_vars func


let rank_and_cluster (vars : VarSet.t) (deps : VarSet.t IM.t) : VarSet.t list =
  (* Search for variables that depend only on themselves *)
  let deps_sorted =
    (List.sort (fun (v1,i1) (v2,i2) -> compare i1 i2)
       (List.map
          (fun (i, card) -> (VarSet.find_by_id vars i, card))
          (IM.to_alist
             (IM.map (fun vs -> VarSet.cardinal vs) deps))))
  in
  let rec satisfy var vdeps satisfied =
    let is_satisfied v =
      match satisfied with
      | [] -> false
      | l -> (List.exists (fun vs -> VarSet.mem v vs) l)
    in
    VarSet.fold
      (fun dep to_sat ->
         if is_satisfied dep then to_sat
         else VarSet.add
             dep
             to_sat)
      vdeps
      (VarSet.singleton var)
  in
  let rec build_clusters vlist accum =
    match vlist with
    | [] -> accum
    | (var, dep_no) :: tl ->
      let cluster, remainder =
        let vdeps = IM.find var.vid deps in
        let cluster = satisfy var vdeps accum in
        cluster,
        (List.filter (fun (v,i) -> not (VarSet.mem v cluster)) tl)
      in
      build_clusters remainder (accum@[cluster])
  in
  snd (List.fold_left
         (fun (last, acc) cluster ->
            let se =
              VarSet.filter
                (fun e -> VarSet.mem e vars)
                (VarSet.union last cluster)
            in
            (se, acc@[se]))
         (VarSet.empty, [])
         (build_clusters deps_sorted []))
