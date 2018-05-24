(**
   This file is part of Parsynt.

    Foobar is free software: you can redistribute it and/or modify
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
open Utils
open FPretty
open FuncTypes
open SymbExe
open Expressions
open ExpressionReduction

let debug = ref false


type auxiliary =
  {
    avar : fnV;
    aexpr : fnExpr;
    afunc : fnExpr;
    depends : VarSet.t;
  }


module AS = Set.Make (struct
    type t = auxiliary
    let compare x y = Pervasives.compare x.avar.vid y.avar.vid
  end)

module AuxSet =
  (struct
    include AS
    let find_id aset id =
      AS.max_elt (AS.filter (fun e -> e.avar.vid = id) aset)
    let mem_id id =
      AS.exists (fun e -> e.avar.vid = id)
    let vars aset =
      VarSet.of_list (List.map (fun a -> a.avar) (AS.elements aset))
  end)

let mkAux v e =
  { avar = v; aexpr = e; afunc = FnLetExpr([]); depends = VarSet.empty; }

let mkAuxF v e f =
  { avar = v; aexpr = e; afunc = f; depends = VarSet.empty; }


let add_left_auxiliary vi =
  add_laux_id vi.vid;
  cur_left_auxiliaries:=
    (VarSet.add vi !cur_left_auxiliaries)

let add_right_auxiliary vi =
  add_raux_id vi.vid;
  cur_right_auxiliaries:=
    (VarSet.add vi !cur_right_auxiliaries)

(** Given a set of auxiliary variables and the associated functions,
    and the set of state variable and a function, return a new set
    of state variables and a function.
*)
let compose xinfo f aux_set =
  let new_ctx = ctx_update_vsets xinfo.context (AuxSet.vars aux_set) in
  let clean_f = remove_id_binding f in
  let replace_index_uses index_set =
    VarSet.fold
      (fun index expr ->
         (replace_expression
            ~in_subscripts:true
            ~to_replace:(mkVarExpr index)
            ~by:(mkVarExpr (index_set index))
            ~ine:expr))
  in
  let new_func, const_exprs =
    let head_assgn, tail_assgn, const_exprs =
      (AuxSet.fold
         (fun aux (head_assgn_list, tail_assgn_list, const_exprs)->
            (** Distinguish different cases :
                - the function is not identity but an accumulator, we add the
                function 'as is' in the loop body.
                TODO : graph analysis to place the let-binding at the right
                position.
                - the function f is the identity, then the auxliary variable
                depends on a finite prefix of the inputs. The expression depends
                on the starting index

                Analyse expressions to respect dependencies.
            *)
            match aux.afunc with
            | FnVar (FnVariable v) when v.vid = aux.avar.vid ->
              (* Replace index by "start index" variable *)
              let aux_expression =
                add_left_auxiliary v;
                replace_index_uses left_index_vi xinfo.context.index_vars aux.aexpr
              in
              (** If the only the "start index" appears, or the aux variable's
                  expression is only a function of the index/input variable, it
                  can be removed from the loop *)
              if
                begin
                  let used_vars = used_in_fnexpr aux_expression in
                  let not_read_vars =
                    VarSet.diff used_vars
                      (VarSet.diff xinfo.context.all_vars new_ctx.state_vars)
                  in
                  let not_read_not_index =
                    VarSet.diff not_read_vars new_ctx.index_vars in
                  (** No other variables than read-only or index *)
                  VarSet.cardinal not_read_not_index = 0
                end
              then
                head_assgn_list@[(FnVariable v, aux_expression)],
                tail_assgn_list,
                const_exprs@[FnVariable v, aux_expression]
              else
                head_assgn_list@[(FnVariable v, aux_expression)],
                tail_assgn_list, const_exprs
            | _ ->
              (** If the function depends only on index and read variables, the
                  final value of the auxiliary depends only on its
                  "final expression"
              *)
              let cur_vi = aux.avar in
              let v = (FnVariable cur_vi) in
              let new_const_exprs =
                const_exprs@
                (if
                  begin
                    let used_vars = used_in_fnexpr aux.afunc in
                    let not_read_vars =
                      VarSet.diff used_vars
                        (VarSet.diff xinfo.context.all_vars xinfo.context.state_vars)
                    in
                    let not_read_not_index =
                      VarSet.diff not_read_vars xinfo.context.index_vars in
                    (** No other variables than read-only or index *)
                    VarSet.cardinal not_read_not_index = 0
                  end
                 then
                   (* The variable doesn't depend on any other state variable *)
                   (add_right_auxiliary cur_vi;
                   [v,
                    replace_index_uses
                      right_index_vi xinfo.context.index_vars aux.afunc])
                 else
                   [])
              in
              (let assgn =
                 [v, aux.afunc]
               in
               let dependencies =
                 VarSet.cardinal (VarSet.inter aux.depends xinfo.context.state_vars)
               in
               if dependencies > 0
               then
                    (* The variable depends on other state variables *)
                 head_assgn_list, tail_assgn_list@assgn, new_const_exprs
               else
                 head_assgn_list@assgn, tail_assgn_list, new_const_exprs))

         aux_set ([], [], []))
    in
    let f = complete_final_state new_ctx.state_vars
        (compose_tail tail_assgn clean_f)
    in
    (compose_head head_assgn f), const_exprs
  in
  (new_ctx, new_func, const_exprs)



let same_aux old_aux new_aux =
  if AuxSet.cardinal old_aux != AuxSet.cardinal new_aux
  then false
  else
    AuxSet.fold
      (fun n_aux same ->
         try
           (let o_aux = AuxSet.find_id old_aux n_aux.avar.vid  in
            if o_aux.afunc = n_aux.afunc then true && same else false)
         with Not_found -> false)
      new_aux
      true

let is_already_computed xinfo aux exprs =
  let candidate_state_variables =
    IM.filter
      (fun i e ->
         (* Replace auxiliary recursive call by state_expr *)
         let e_rep =
           replace_expression ~in_subscripts:false
             ~to_replace:(mkVarExpr aux.avar)
             ~by:(FnVar (FnVariable
                           (VarSet.find_by_id xinfo.context.state_vars i)))
             ~ine:aux.afunc
         in
         e_rep @= e) exprs
  in
  IM.cardinal candidate_state_variables > 0

let remove_duplicate_auxiliaries xinfo aux_set input_func =
  let exprs, inputs = unfold_once ~silent:true xinfo input_func in
  AuxSet.filter
    (fun aux ->
       not (is_already_computed xinfo aux exprs))
    aux_set



let reduction_with_warning ctx expr =
  let reduced_expression = reduce_full ctx expr in
  if (expr = reduced_expression) && !debug then
    begin
      Format.fprintf Format.std_formatter
        "%sWarning%s : expression @;%a@; unchanged after \
         reduction with state %a @; and expressions %a @."
        (PpTools.color "red") PpTools.color_default
        FPretty.pp_fnexpr reduced_expression
        VarSet.pp_var_names ctx.state_vars
        (fun fmt a -> FPretty.pp_expr_set fmt a) ctx.costly_exprs
    end
  else ();
  reduced_expression


let reset_index_expressions xinfo aux =
    IM.fold
      (fun idx_id idx_expr e ->
         try
           (* Replace the index expressions by the index itself *)
           replace_expression ~in_subscripts:true
             ~to_replace:idx_expr
             ~by:(FnVar
                (FnVariable
                   (VarSet.find_by_id xinfo.context.index_vars idx_id)))
             ~ine:e
         with Not_found ->
           Format.eprintf "@.Index with id %i not found in %a.@."
             idx_id VarSet.pp_var_names xinfo.context.index_vars;
           raise Not_found
      )
      xinfo.index_exprs
      aux

let replace_available_vars xinfo xinfo_aux ce =
   IM.fold
      (fun vid e ce ->
         let vi = VarSet.find_by_id xinfo.context.state_vars vid in
         replace_AC
           xinfo_aux.context
           ~to_replace:(FnVar (FnVariable vi))
           ~by:(accumulated_subexpression vi e)
           ~ine:ce)
      xinfo_aux.state_exprs
      ce
