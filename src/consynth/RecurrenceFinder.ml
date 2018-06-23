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
open Expressions
open Format
open FnPretty
open Fn
open SymbExe
open Utils
open VUtils

let _aux_prefix_ = ref "aux"
let aux_prefix s = _aux_prefix_ := "aux_"^s

let replace_cell aux j e =
  match aux.aexpr with
  | FnVector el ->
    replace_expression
      (mkVarExpr ~offsets:[FnConst (CInt j)] aux.avar)
      (el >> j)
      e
  | ex ->
    replace_expression
      (mkVarExpr ~offsets:[FnConst (CInt j)] aux.avar)
      ex
      e

let exec_foldl (xinfo : exec_info) (aux : auxiliary) (acc : auxiliary) : fnExpr =
  let xinfo' =
    {xinfo with context = {xinfo.context with state_vars = VarSet.empty}}
  in
  let unfold_op e = fst (unfold_expr xinfo' e) in
  let acc_index_var = VarSet.max_elt acc.depends in
  let e_unfolded =
    match aux.afunc with
    | FnVector el ->
      let _, _, elements =
        List.fold_left
          (fun (j, scacc, elts) e ->
             let scacc' =
               replace_expression_in_subscripts
                 (mkVarExpr acc_index_var) (* TODO replace by j index *)
                 (FnConst (CInt j))
                 (replace_expression
                    (mkVarExpr acc.avar)
                    scacc
                    (unfold_op acc.afunc))
             in
             j + 1,
             scacc',
             elts@[replace_expression
                     (mkVarExpr acc.avar)
                     scacc'
                     (unfold_op e)])
          (0, acc.aexpr, [])
          el
      in
      FnVector elements
    | _ ->
      failhere __FILE__ "find_accumulator" "Got non-vector while looking for foldl."
  in
  e_unfolded


let exec_foldr (xinfo : exec_info) (aux : auxiliary) (acc : auxiliary) : fnExpr =
  let xinfo' =
    {xinfo with context = {xinfo.context with state_vars = VarSet.empty}}
  in
  let unfold_op e = fst (unfold_expr xinfo' e) in
  let acc_index_var = VarSet.max_elt acc.depends in
  let accumulate_foldr (j, scacc, elts) e =
    (* Compute the accumulator *)
    let scacc' =
      replace_expression_in_subscripts
        (mkVarExpr acc_index_var)
        (FnConst (CInt (j - 1)))
        (replace_expression
           (mkVarExpr acc.avar)
           scacc
           (unfold_op acc.afunc))
    in
    j - 1,
    scacc',
    elts@[
      (* Replace the accummulator by its expression *)
      replace_expression
        (mkVarExpr acc.avar)
        scacc
        (unfold_op e)]
  in
  let e_unfolded =
    match aux.afunc with
    | FnVector el ->
      (* Replace the accumulated part *)
      let _, _, elements =
        List.fold_left accumulate_foldr
          (List.length el - 1,
           replace_expression_in_subscripts
             (mkVarExpr acc_index_var)
             (FnConst (CInt (List.length el - 1)))
             acc.aexpr,
           [])
          el
      in
      (* Replace the self-recursive part. *)
      let elements' =
        List.mapi (fun i e -> replace_cell aux i e) elements
      in
      FnVector elements'
    | _ ->
      failhere __FILE__ "find_accumulator" "Got non-vector while looking for foldr."
  in
  e_unfolded


let replace_foldr_accu (accu : auxiliary) (el : fnExpr list) =
  let acc_index_var = VarSet.max_elt accu.depends in
  let accumulate_foldr (j, scacc, elts) e =
    (* Compute the accumulator *)
    let scacc' =
      replace_expression
        (mkVarExpr accu.avar)
        scacc
        (replace_expression_in_subscripts
           (mkVarExpr acc_index_var)
           (FnConst (CInt (j - 1)))
           accu.afunc)
    in
    j - 1,
    scacc',
    elts@[
      (* Replace the accummulator by its expression *)
      replace_expression
        scacc
        (mkVarExpr accu.avar)
        e]
  in
  third
    (List.fold_left accumulate_foldr
       (List.length el - 1,
        replace_expression_in_subscripts
          (mkVarExpr acc_index_var)
          (FnConst (CInt (List.length el - 1)))
          accu.aexpr,
        [])
       el)


let find_accumulator (xinfo : exec_info ) (ne : fnExpr) : AuxSet.t -> AuxSet.t =

  let find_scalar_accumulator aux =
    let xinfo' =
      {xinfo with context = {xinfo.context with state_vars = VarSet.empty}}
    in
    let unfold_op e = fst (unfold_expr xinfo' e) in
    let e_unfolded =
      replace_expression (mkVarExpr aux.avar) aux.aexpr (unfold_op aux.afunc)
    in
    printf "@[<v 4>Scalar accumulation?@;%a@;%s==%s@;%a@.%b@]@."
      cp_fnexpr e_unfolded
      (PpTools.color "red") (PpTools.color_default)
      cp_fnexpr ne (e_unfolded @= ne);
    e_unfolded @= ne
  in

  let find_map_accumulator aux =
    let xinfo' =
      {xinfo with context = {xinfo.context with state_vars = VarSet.empty}}
    in
    let unfold_op e = fst (unfold_expr xinfo' e) in
    let e_unfolded =
      match aux.afunc with
      | FnVector el ->
        FnVector(List.mapi (fun i e -> replace_cell aux i (unfold_op e)) el)
      | e ->
        replace_expression (mkVarExpr aux.avar) aux.aexpr (unfold_op e)
    in
    printf "@[<v 4>Map accumulation?@;%a@;%s==%s@;%a@.%b@]@."
      cp_fnexpr e_unfolded
      (PpTools.color "red") (PpTools.color_default)
      cp_fnexpr ne (e_unfolded @= ne);
    e_unfolded @= ne
  in

  let find_foldl_accumulator aux acc =
    let e_unfolded = exec_foldl xinfo aux acc in
    printf "@[<v 4>Foldl accumulation?@;%a@;%s==%s@;%a@.%b@]@."
      cp_fnexpr e_unfolded
      (PpTools.color "red") (PpTools.color_default)
      cp_fnexpr ne (e_unfolded @= ne);
    e_unfolded @= ne
  in

  let find_foldr_accumulator aux acc =
   let e_unfolded = exec_foldr xinfo aux acc in
    printf "@[<v 4>Foldr accumulation?@;%a@;%s==%s@;%a@.%b@]@."
      cp_fnexpr e_unfolded
      (PpTools.color "red") (PpTools.color_default)
      cp_fnexpr ne
      (e_unfolded @= ne);
    e_unfolded @= ne
  in

  AuxSet.filter
    (fun aux ->
       match aux.atype with
       | Scalar -> find_scalar_accumulator aux
       | Map -> find_map_accumulator aux
       | FoldL acc -> find_foldl_accumulator aux acc
       | FoldR acc -> find_foldr_accumulator aux acc
    )


let collect_input_subscripts (ctx : context) (e : fnExpr) : ES.t =
  let rec collect v =
    match v with
    | FnArray(a, e) -> ES.singleton e
    | _ -> ES.empty
  in
  rec_expr2
    {
      join = ES.union;
      init = ES.empty;
      case = (fun e -> false);
      on_case = (fun f e -> ES.empty);
      on_var = collect;
      on_const = (fun c -> ES.empty);
    } e



let is_map (ctx : context) (el : fnExpr list) : bool =
  List.for_all2
    (fun expr i ->
       let iset = collect_input_subscripts ctx expr in
       ES.cardinal iset = 1 &&
       (match ES.max_elt iset with
        | FnConst (CInt j) -> j = i
        | _ -> false))
    el
    (List.mapi (fun i a -> i) el)


let is_foldl (ctx : context) : fnExpr list -> bool =
  ListTools.for_all_i
    (fun (i,expr) ->
       let iset = collect_input_subscripts ctx expr in
       ES.cardinal iset <= (i + 1) &&
       ES.for_all
         (fun e ->
            match e with
            | FnConst (CInt j) -> j <= i
            | _ -> false) iset)


let is_foldr (ctx : context) (el : fnExpr list) : bool =
  let n = List.length el in
  ListTools.for_all_i
    (fun (i, expr) ->
       let iset = collect_input_subscripts ctx expr in
       ES.cardinal iset <= (i + 1) &&
       ES.for_all
         (fun e ->
            match e with
            | FnConst (CInt j) -> j >= (n - (i + 1))
            | _ -> false) iset) el


let create_foldl (ctx : context) (var : fnLVar) (sc_acc : fnV) (el : fnExpr list) =
  []

let create_foldr (ctx : context) (var : fnLVar) (sc_acc : fnV) (el : fnExpr list) =
  let acc_index = mkFnVar "j" Integer in
  let acc_func =
    assert (List.length el >= 3);
    replace_expression_in_subscripts
      ~to_replace:(FnConst (CInt 1))
      ~by:(mkVarExpr acc_index)
      ~ine:
        (replace_AC ctx ~to_replace:(el >> 0) ~by:(mkVarExpr sc_acc) ~ine:(el >>1))
  in
  let t = FoldR
      {
        avar = sc_acc;
        aexpr =
          replace_expression_in_subscripts
            ~to_replace:(FnConst (CInt 0))
            ~by:(mkVarExpr acc_index)
            ~ine:(el >> 0);
        afunc = acc_func;
        atype = Scalar;
        depends = VarSet.singleton acc_index;
      }
  in
  [FnVector(List.map (fun e -> mkVarExpr sc_acc) el), t]


let find_row_function (el : fnExpr list) =
  el



let get_base_accus (ctx : context) (var : fnLVar) (expr : fnExpr) :
  (fnExpr * aux_comp_type) list =

  match expr with
  | FnBinop (op, expr1, expr2) when is_constant expr1 && is_constant expr2 ->
    [FnBinop (op, FnVar var, expr2), Scalar;
     FnBinop (op, expr1, FnVar var), Scalar;
     FnBinop (op, expr1, expr2), Scalar]

  | FnVector el ->
    if is_map ctx el then
      [FnVector (List.mapi (fun i e -> FnVar(FnArray(var, FnConst(CInt i)))) el), Map]
    else if is_foldl ctx el then
      let scalar_acc = mkFnVar "foldr_acc" (type_of (List.hd el)) in
      create_foldl ctx var scalar_acc el

    else if is_foldr ctx el then
      let scalar_acc = mkFnVar "foldr_acc" (type_of (List.hd el)) in
      create_foldr ctx var scalar_acc el

    else
      [expr, Map]

  | _ -> [expr, Scalar]



(** make_rec_calls replaces the expression of the auxiliary aux in the expression
    expr' by the variable var, creating the accumulation function for the new auxiliary
    var that is being created.
*)
let make_rec_calls
  (xinfo : exec_info)
  (var, aux : fnV * auxiliary)
  (expr' : fnExpr) : fnExpr list =

  let make_cell_rec_call el' vecs (j, e) =
    let rcalls =
      replace_many_AC e (mkVarExpr ~offsets:[FnConst (CInt j)] var) (el' >> j) 1
    in
    if List.length vecs = 0 then
      List.map (fun rcall -> [rcall]) rcalls
    else if List.length vecs <= List.length rcalls then
      List.map2 (fun vec rcall -> vec@[rcall]) vecs (ListTools.take (List.length vecs) rcalls)
    else
      List.map2 (fun vec rcall -> vec@[rcall]) (ListTools.take (List.length rcalls) vecs) rcalls

  in

  match aux.atype, aux.aexpr, expr' with
  | Map, FnVector el, FnVector el' ->
    assert (List.length el = List.length el');
    List.map (fun l -> FnVector l)
      (List.fold_left (make_cell_rec_call el') [] (List.mapi (fun i e -> (i,e)) el))

  | FoldR accu, FnVector el, FnVector el' ->
    assert (List.length el = List.length el');
    let rcalls =
      List.map
        (fun l -> FnVector (replace_foldr_accu accu l))
      (List.fold_left (make_cell_rec_call el') [] (List.mapi (fun i e -> (i,e)) el))
    in
    rcalls

  | FoldL accu, _, _ -> failwith "TODO"

  | Scalar, _, _ -> replace_many aux.aexpr (mkVarExpr var) expr' 1

  | _, _, _ -> replace_many aux.aexpr (mkVarExpr var) expr' 1


let pick_best_recfunc fexpr_l =
  List.hd fexpr_l


let update_accumulator
    (xinfo : exec_info)
    (xinfo_aux : exec_info)
    (expr : fnExpr)
    (candidates : AuxSet.t)
    (aux_set' : AuxSet.t)  =

  let update_one_accu candidate_aux aux_set' =
    (* Create a new auxiliary to avoid deleting the old one *)
    let new_vi =
      mkFnVar (get_new_name ~base:!_aux_prefix_) (type_of candidate_aux.aexpr)
    in
    (**
       Replace the old expression of the auxiliary by the auxiliary. Be careful
       not to add too many recursive calls. Try to replace it only once, to
       avoid spurious recursive locations.
    *)
    let replace_aux = make_rec_calls xinfo (new_vi, candidate_aux) expr in
    let new_f =
      pick_best_recfunc (List.map (reset_index_expressions xinfo) replace_aux)
    in

    let new_auxiliary =
      {
        avar = new_vi;
        aexpr = replace_available_vars xinfo xinfo_aux expr;
        afunc = new_f;
        atype = candidate_aux.atype;
        depends = used_in_fnexpr new_f;
      }
    in
    if !verbose then
      printf
        "@[<v 4>[INFO] Updated@;%s,@;now has accumulator :@;%a@;and expression@;%a@]@."
        new_vi.vname cp_fnexpr new_f cp_fnexpr new_auxiliary.aexpr;

    AuxSet.add_new_aux xinfo.context aux_set' new_auxiliary
  in
  update_one_accu (AuxSet.max_elt candidates) aux_set'
