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
open Utils
open FPretty
open FuncTypes
open SymbExe
open Expressions
open ExpressionReduction
open Utils.PpTools

let debug = ref false


type auxiliary =
  {
    avar : fnV;
    aexpr : fnExpr;
    afunc : fnExpr;
    depends : VarSet.t;
  }

let pp_auxiliary fmt aux =
  fprintf fmt
    "@[<v>@[<v 2>%s =@;%a.@]@;@[<v 2>f =@;%a@]@;"
    aux.avar.vname cp_fnexpr aux.aexpr cp_fnexpr aux.afunc

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
    let rec inters al =
      match al with
      | [] -> empty
      | [a] -> a
      | hd :: tl -> inter hd (inters tl)

    let exists_vector j f a =
      exists
        (fun elt ->
           match elt.aexpr with
           | FnVector el ->
             (List.length el > j &&
              f (el >> j))
           | _ -> false) a

    let filter_vector j f a =
      filter
        (fun elt ->
           match elt.aexpr with
           | FnVector el ->
             (List.length el > j &&
              f (el >> j))
           | _ -> false) a


    let add_new_aux
        (ctx : context) (aux_set : t) (aux_to_add : auxiliary) : t =
      let same_expr_and_func =
        filter
          (fun aux ->
             let func = replace_AC
                 ctx
                 ~to_replace:(mkVarExpr aux.avar)
                 ~by:(mkVarExpr aux_to_add.avar)
                 ~ine:aux.afunc
             in
             aux.aexpr @= aux_to_add.aexpr && func @= aux_to_add.afunc)
          aux_set
      in
      if cardinal same_expr_and_func > 0 then aux_set
      else
        begin
          printf
            "@.%s%s Adding new auxiliary :%s %s.@.Expression : %a.@.Function : %a@."
            (color "b-green") (color "black") color_default
            aux_to_add.avar.vname
            cp_fnexpr aux_to_add.aexpr cp_fnexpr aux_to_add.afunc;

          add aux_to_add aux_set
        end

    let pp_aux_set fmt a =
      iter (fun aux -> pp_auxiliary fmt aux) a
  end)

let mkAux v e =
  { avar = v; aexpr = e; afunc = wrap_state []; depends = VarSet.empty; }

let mkAuxF v e f =
  { avar = v; aexpr = e; afunc = f; depends = VarSet.empty; }


let replace_index_uses index_set =
  VarSet.fold
    (fun index expr ->
       (replace_expression
          ~in_subscripts:true
          ~to_replace:(mkVarExpr index)
          ~by:(mkVarExpr (index_set index))
          ~ine:expr))

let add_to_inner_loop_body
    (aux : auxiliary) (inner_loop : prob_rep) (v, e : fnLVar * fnExpr) :
  prob_rep =
  let ctx = inner_loop.scontext in
  let new_stv = VarSet.add aux.avar ctx.state_vars in
  let new_body =
    complete_final_state new_stv
      (compose_tail [v, e] inner_loop.main_loop_body)
  in
  printf "New body:@.%a@." pp_fnexpr new_body;
  {inner_loop with
   scontext =
     { ctx with
       state_vars = new_stv;
       all_vars = VarSet.add aux.avar ctx.state_vars;
       used_vars = VarSet.union ctx.used_vars (used_in_fnexpr e);
     };
   main_loop_body = new_body;
   memless_sketch =
     Sketch.Join.build_from_solution_inner
       [mkVarExpr (VarSet.max_elt ctx.index_vars)]
       new_stv
       inner_loop.reaching_consts
       (inner_loop.memless_solution, new_body);
  }

let clear_solution (prob : prob_rep) : prob_rep =
  {
    prob with
    memless_solution = empty_record;
    join_solution = empty_record;
  }

(** Given a set of auxiliary variables and the associated functions,
    and the set of state variable and a function, return a new set
    of state variables and a function.
*)
let compose problem xinfo aux_set =
  let f = InnerFuncs.no_join_inlined_body problem in
  let new_ctx = ctx_update_vsets xinfo.context (AuxSet.vars aux_set) in
  let clean_f = remove_id_binding f in
  let compose_case_single xinfo aux (hal, tal) v =
    (* Replace index by "start index" variable *)
    let aux_expression =
      add_left_auxiliary v;
      replace_index_uses
        left_index_vi xinfo.context.index_vars aux.aexpr
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
      hal@[(FnVariable v, aux_expression)],
      tal
    else
      hal@[(FnVariable v, aux_expression)], tal
  in
  let compose_case_default xinfo aux (hal, tal) =
    let cur_vi = aux.avar in
    let v = (FnVariable cur_vi) in
    let assgn =
       [v, aux.afunc]
     in
     let dependencies =
       VarSet.cardinal (VarSet.inter aux.depends xinfo.context.state_vars)
     in
     if dependencies > 0
     then
       (* The variable depends on other state variables *)
       hal, tal@assgn
     else
       hal@assgn, tal
  in
  let compose_case_vector
      (xinfo : exec_info)
      (aux : auxiliary)
      (el :fnExpr list)
      (il : prob_rep list) : prob_rep list =
    List.map
      (fun inner_loop ->
         let j = VarSet.max_elt (get_index_varset inner_loop) in
         let jexprs =
           List.mapi
             (fun i e ->
                replace_expression
                  ~in_subscripts:true
                  ~to_replace:(FnConst (CInt i))
                  ~by:(mkVarExpr j)
                  ~ine:e) el
         in
         if List.length jexprs > 1 &&
            List.for_all (fun e -> e @= (List.hd jexprs)) jexprs
         then
           let binding =
             FnVariable aux.avar,
             FnArraySet(mkVarExpr aux.avar, mkVarExpr j, List.hd jexprs)
           in
           clear_solution (add_to_inner_loop_body aux inner_loop binding)

         else
           (if !debug then
              printf "[WARNING] Skipped auxiliary %s. Unrecognized shape.@."
              aux.avar.vname;
            inner_loop))
      il
  in
  let new_func, inner_loops =
    let head_assgn, tail_assgn, inner_loops =
      (AuxSet.fold
         (fun aux (hl, tl, il)->
            (** Distinguish different cases :
                - the function is not identity but an accumulator, we add the
                function 'as is' in the loop body.
                TODO : graph analysis to place the let-binding at the right
                position.
                - the function is a vector. Deduce the recursion to add in the
                inner loop.
                - the function f is the identity, then the auxliary variable
                depends on a finite prefix of the inputs. The expression depends
                on the starting index

                Analyse expressions to respect dependencies.
            *)
            match aux.afunc with
            | FnVar (FnVariable v) when v.vid = aux.avar.vid ->
              let hl', tl' =
                compose_case_single xinfo aux (hl, tl) v
              in
              (hl', tl', il)

            | FnVector el ->
              let il' = compose_case_vector xinfo aux el il in
              (hl, tl, il')

            | _ ->
              let hl', tl' =
                compose_case_default xinfo aux (hl, tl)
              in
              (hl', tl', il)
              (** If the function depends only on index and read variables, the
                  final value of the auxiliary depends only on its
                  "final expression"
              *)
         )

         aux_set ([], [], problem.inner_functions))
    in
    let f = complete_final_state new_ctx.state_vars
        (compose_tail tail_assgn clean_f)
    in
    (compose_head head_assgn f), inner_loops
  in
  {
    problem with
    scontext = new_ctx;
    main_loop_body = new_func;
    inner_functions = inner_loops;
  }



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
  let xinfo' = unfold_once ~silent:true xinfo input_func in
  AuxSet.filter
    (fun aux ->
       not (is_already_computed xinfo aux xinfo'.state_exprs))
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

let replace_available_vars
    (xinfo : exec_info) (xinfo_aux : exec_info) (ce : fnExpr): fnExpr =
  let aux se expr j =
    IM.fold
      (fun vid st_e ine ->
         let vi = VarSet.find_by_id xinfo.context.state_vars vid in
         let tr =
           match vi.vtype with
           | Vector _ when j >= 0->
             mkVarExpr ~offsets:[FnConst(CInt j)] vi
           | _ -> mkVarExpr vi
         in
         let by =
           match st_e with
           | FnVector stel when j >= 0 ->
             accumulated_subexpression (vi, j) (stel >> j)
           | e ->
             accumulated_subexpression (vi, j) e
         in
         replace_AC xinfo_aux.context tr by ine)
      se
      expr
  in
  match ce with
  | FnVector el ->
    FnVector (List.mapi (fun j e -> aux xinfo_aux.state_exprs e j) el)
  | _ ->
    aux xinfo_aux.state_exprs ce (-1)


let rec is_stv vset expr =
  match expr with
  | FnUnop (_, FnVar v)
  | FnVar v ->
    begin
      try
        VarSet.mem (check_option (vi_of v)) vset
      with Failure s -> false
    end
  | FnCond (c, e1, e2) -> is_stv vset c
  | _ -> false


let rec collect_state_lvars (expr : fnExpr) : fnLVar =
  match expr with
  | FnUnop (_, FnVar v)
  | FnVar v -> v
  | FnCond (c, e1, e2) -> collect_state_lvars c
  | _ -> failwith "Not an stv."


let candidates (vset : VarSet.t) (e : fnExpr) =
  let is_candidate =
    function
    | FnBinop (_, e1, e2)
    | FnCond (_, e1, e2) ->
      (** One of the operands must be a state variable
          but not the other *)
      (is_stv vset e1 && (not (fn_uses vset e2))) ||
      (is_stv vset e2 && (not (fn_uses vset e1)))
    (* Special rule for conditionals *)
    | _ ->  false
  in

  let handle_candidate f =
    function
    | FnBinop (_, e1, e2) ->
      begin
        match e1, e2 with
        | FnCond(c, _, _), estv when is_stv vset estv ->
          [collect_state_lvars estv, c]
        | estv, FnCond(c, _, _) when is_stv vset estv ->
          [collect_state_lvars estv, c]
        | e, estv  when is_stv vset estv -> [collect_state_lvars estv, e]
        | estv, e when is_stv vset estv -> [collect_state_lvars estv, e]
        | _ -> []
      end

    | FnCond (_, e1, e2) ->
      if is_stv vset e1 then
        [collect_state_lvars e1, e2]
      else
        [collect_state_lvars e1, e2]
    | _ ->  []
  in

  let collected_candidates =
    rec_expr
      (fun a b -> a@b)
      []
      is_candidate
      handle_candidate
      (fun c -> [])
      (fun v -> [])
      e
  in
  VarSet.fold
    (fun ve l ->
       let matching_candidates =
         List.map (fun (a,b) -> b)
           (List.filter (fun (s, es) -> ve = var_of_fnvar s)
              collected_candidates)
       in (ve, List.rev matching_candidates)::l)
    vset []


(** Find in an auxliary set the auxilairies matching EXACTLY the expression *)
let find_matching_aux (to_match : fnExpr) (auxset : AuxSet.t) =
  AuxSet.filter (fun aux -> aux.aexpr @= to_match) auxset

let find_matching_vectaux (to_match : fnExpr) (j : int) (auxset : AuxSet.t) =
  AuxSet.filter_vector j (fun aexpr_j -> aexpr_j @= to_match) auxset


let find_subexpr (top_expr : fnExpr) (auxs : AuxSet.t) =
  let scalar_subexpr expr =
    rec_expr
      (fun a b -> AuxSet.union a b) AuxSet.empty
      (fun e ->
         AuxSet.exists
           (fun aux -> aux.aexpr @= e) auxs)
      (fun f e -> find_matching_aux e auxs)
      (fun c ->  AuxSet.empty) (fun v ->  AuxSet.empty)
      expr
  in
  let vector_subexpr expr j =
    rec_expr
      (fun a b -> AuxSet.union a b) AuxSet.empty
      (fun e -> AuxSet.exists_vector j (fun expr_j -> expr_j @= e) auxs)
      (fun f e -> find_matching_vectaux e j auxs)
      (fun c ->  AuxSet.empty) (fun v ->  AuxSet.empty)
      expr
  in
  match top_expr with
  | FnVector el ->
    AuxSet.inters (List.mapi (fun j ej -> vector_subexpr ej j) el)

  | _ -> scalar_subexpr top_expr



(** Check that the function applied to the old expression gives
    the new expression. *)
let find_accumulator (xinfo : exec_info ) (ne : fnExpr) : AuxSet.t -> AuxSet.t =
  AuxSet.filter
    (fun aux ->
       let xinfo' =
         {xinfo with context = {xinfo.context with state_vars = VarSet.empty}}
       in
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
       in
       let unfold_op e = fst (unfold_expr xinfo' e) in
       let e_unfolded =
         match aux.afunc with
         | FnVector el ->
           FnVector(List.mapi (fun i e -> replace_cell aux i (unfold_op e)) el)
         | e ->
           replace_expression (mkVarExpr aux.avar) aux.aexpr (unfold_op e)
       in
       printf "@[<v 4>Accumulation?@;%a==@;%a@.%b@]@."
         cp_fnexpr e_unfolded cp_fnexpr ne (e_unfolded @= ne);
       e_unfolded @= ne)


let find_computed_expressions
    (i :int) (xinfo : exec_info) (xinfo_aux : exec_info) (e : fnExpr) : fnExpr =
  let vals_at_j xinfo j =
    let from_intermediate_vals =
      IM.map
        (fun el -> if List.length el > j then Some (el >> j) else None)
        xinfo.intermediate_states
    in
    let from_vectors_of_state =
      IM.map
        (fun e ->
           match e with
           | FnVector el when List.length el > j -> Some (el >> j)
           | e -> None)
        xinfo.state_exprs
    in
    IM.map check_option (IM.join_opt from_vectors_of_state from_intermediate_vals)
  in
  let aux state_exprs e j =
    IM.fold
      (fun vid e ce ->
         let vi = VarSet.find_by_id xinfo.context.state_vars vid in
         let by =
           match vi.vtype with
           | Vector (t,_) -> mkVarExpr ~offsets:[FnConst(CInt j)] vi
           | _ -> mkVarExpr vi
         in
         let tr = (accumulated_subexpression (vi, j) e) in
         if is_constant tr then
           ce
         else
           replace_AC xinfo_aux.context ~to_replace:tr ~by:by ~ine:ce)
      state_exprs e
  in
  if i > 0 then
    match e with
    | FnVector el ->
      FnVector
        (List.mapi
           (fun j e ->
              aux (vals_at_j xinfo_aux j) e j) el)

    | _ -> aux xinfo_aux.state_exprs e (-1)
  else
    e

let new_const_exprs xinfo aux cur_vi v =
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
