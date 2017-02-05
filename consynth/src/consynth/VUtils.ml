open Format
open Utils
open SPretty
open SketchTypes
open SymbExe
open Expressions
open ExpressionReduction

let debug = ref false

module C = Cil

type auxiliary =
  {
    avarinfo : C.varinfo;
    aexpr : skExpr;
    afunc : skExpr;
    depends : VS.t;
  }

let add_left_auxiliary vi =
  SketchJoin.left_auxiliaries:=
    (VS.add vi !SketchJoin.left_auxiliaries)

let add_right_auxiliary vi =
  SketchJoin.right_auxiliaries:=
    (VS.add vi !SketchJoin.right_auxiliaries)

(** Given a set of auxiliary variables and the associated functions,
    and the set of state variable and a function, return a new set
    of state variables and a function.
*)
let compose xinfo f aux_vs aux_ef =
  let new_ctx = ctx_update_vsets xinfo.context aux_vs in
  let clean_f = remove_id_binding f in
  let replace_index_uses index_set =
    VS.fold
      (fun index expr ->
         (T.replace_expression
            ~in_subscripts:true
            ~to_replace:(T.mkVarExpr index)
            ~by:(T.mkVarExpr (index_set index))
            ~ine:expr))
  in
  let new_func, const_exprs =
    let head_assgn, tail_assgn, const_exprs =
      (IM.fold
         (fun aux_vid aux (head_assgn_list, tail_assgn_list, const_exprs) ->
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
            | T.SkVar (T.SkVarinfo v) when v.Cil.vid = aux_vid ->
              (* Replace index by "start index" variable *)
              let aux_expression =
                add_left_auxiliary v;
                replace_index_uses T.left_index_vi xinfo.context.index_vars aux.aexpr
              in
              (** If the only the "start index" appears, or the aux variable's
                  expression is only a function of the index/input variable, it
                  can be removed from the loop *)
              if
                begin
                  let used_vars = used_in_skexpr aux_expression in
                  let not_read_vars =
                    VS.diff used_vars
                      (VS.diff xinfo.context.all_vars new_ctx.state_vars)
                  in
                  let not_read_not_index =
                    VS.diff not_read_vars new_ctx.index_vars in
                  (** No other variables than read-only or index *)
                  VS.cardinal not_read_not_index = 0
                end
              then
                head_assgn_list@[(T.SkVarinfo v, aux_expression)],
                tail_assgn_list,
                const_exprs@[T.SkVarinfo v, aux_expression]
              else
                head_assgn_list@[(T.SkVarinfo v, aux_expression)],
                tail_assgn_list, const_exprs
            | _ ->
              (** If the function depends only on index and read variables, the
                  final value of the auxiliary depends only on its
                  "final expression"
              *)
              let cur_vi = (VSOps.find_by_id aux_vid aux_vs) in
              let v = (T.SkVarinfo cur_vi) in
              let new_const_exprs =
                const_exprs@
                (if
                  begin
                    let used_vars = used_in_skexpr aux.afunc in
                    let not_read_vars =
                      VS.diff used_vars
                        (VS.diff xinfo.context.all_vars xinfo.context.state_vars)
                    in
                    let not_read_not_index =
                      VS.diff not_read_vars xinfo.context.index_vars in
                    (** No other variables than read-only or index *)
                    VS.cardinal not_read_not_index = 0
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
                 VS.cardinal (VS.inter aux.depends xinfo.context.state_vars)
               in
               if dependencies > 0
               then
                    (* The variable depends on other state variables *)
                 head_assgn_list, tail_assgn_list@assgn, new_const_exprs
               else
                 head_assgn_list@assgn, tail_assgn_list, new_const_exprs))

         aux_ef ([], [], []))
    in
    let f = complete_final_state new_ctx.state_vars
        (T.compose_tail tail_assgn clean_f)
    in
    (T.compose_head head_assgn f), const_exprs
  in
  (new_ctx, new_func, const_exprs)



let same_aux old_aux new_aux =
  if IM.cardinal old_aux != IM.cardinal new_aux
  then false
  else
    IM.fold
      (fun n_vid n_aux same ->
         try
           (let o_aux = IM.find n_vid old_aux in
            if o_aux.afunc = n_aux.afunc then true && same else false)
         with Not_found -> false)
      new_aux
      true

let is_already_computed xinfo (aux_id, aux_vs, func_expr) exprs =
  let candidate_state_variables =
    IM.filter
      (fun i e ->
         (* Replace auxiliary recursive call by state_expr *)
         let e_rep =
           replace_expression ~in_subscripts:false
             ~to_replace:(SkVar (SkVarinfo (VSOps.find_by_id aux_id aux_vs)))
             ~by:(SkVar (SkVarinfo
                           (VSOps.find_by_id i xinfo.context.state_vars)))
             ~ine:func_expr
         in
         e_rep @= e) exprs
  in
  IM.cardinal candidate_state_variables > 0

let remove_duplicate_auxiliaries xinfo (aux_vs, aux_ef) input_func =
  let exprs, inputs = unfold_once ~silent:true xinfo input_func in
  let new_aux_ef =
    IM.filter
      (fun vid aux ->
         not (is_already_computed xinfo (vid, aux_vs, aux.afunc) exprs))
      aux_ef
  in
  (VS.filter (fun vi -> IM.mem vi.C.vid new_aux_ef) aux_vs), new_aux_ef


let reduction_with_warning ctx expr =
  let reduced_expression = reduce_full ctx expr in
  if (expr = reduced_expression) && !debug then
    begin
      Format.fprintf Format.std_formatter
        "%sWarning%s : expression @;%a@; unchanged after \
         reduction with state %a @; and expressions %a @."
        (PpHelper.color "red") PpHelper.default
        SPretty.pp_skexpr reduced_expression
        VSOps.pvs ctx.state_vars
        (fun fmt a -> SPretty.pp_expr_set fmt a) ctx.costly_exprs
    end
  else ();
  reduced_expression


let reset_index_expressions xinfo aux =
    IM.fold
      (fun idx_id idx_expr e ->
         try
           (* Replace the index expressions by the index itself *)
           T.replace_expression ~in_subscripts:true
             ~to_replace:idx_expr
             ~by:(T.SkVar
                (T.SkVarinfo
                   (VSOps.find_by_id idx_id xinfo.context.index_vars)))
             ~ine:e
         with Not_found ->
           Format.eprintf "@.Index with id %i not found in %a.@."
             idx_id VSOps.pvs xinfo.context.index_vars;
           raise Not_found
      )
      xinfo.index_exprs
      aux

let replace_available_vars xinfo xinfo_aux ce =
   IM.fold
      (fun vid e ce ->
         let vi = VSOps.find_by_id vid xinfo.context.state_vars in
         replace_AC
           xinfo_aux.context
           ~to_replace:(T.SkVar (T.SkVarinfo vi))
           ~by:(accumulated_subexpression vi e)
           ~ine:ce)
      xinfo_aux.state_exprs
      ce
