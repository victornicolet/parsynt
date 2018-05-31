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
open FPretty
open ExpressionReduction
open SymbExe
open VUtils
open Expressions
open FuncTypes
open Utils
open Utils.PpTools

exception VariableDiscoveryError of string

let debug = ref false
let verbose = ref false
let debug_dev = ref true

let _aux_prefix_ = ref "aux"
let aux_prefix s = _aux_prefix_ := "aux_"^s

let max_exec_no =
  ref (Conf.get_conf_int "variable_discovery_max_unfoldings")

let unfold_index xinfo idx_update =
  let ix =
    { context =
        { state_vars = xinfo.context.index_vars ;
          index_vars = VarSet.empty;
          used_vars = VarSet.empty;
          all_vars = VarSet.empty;
          costly_exprs = ES.empty;};
      state_exprs = xinfo.index_exprs ;
      index_exprs = IM.empty ;
      inputs = ES.empty;
    }
  in
  let full_map, _ = unfold_once ~silent:true ix idx_update in
  VarSet.fold
    (fun vi map -> IM.add vi.vid (IM.find vi.vid full_map) map)
    xinfo.context.index_vars IM.empty


(* Is var reintialized in one of problem's inner loops? *)
let is_reinitialized problem var =
  List.exists
    (fun in_pb ->
       VarSet.mem var in_pb.scontext.state_vars &&
       IM.mem var.vid in_pb.reaching_consts)
    problem.inner_functions


(* Check well-formedness of inputs. *)
let rec check_wf input_function stv  =
  match input_function with
  | FnLetExpr assignments ->
    input_function
  | FnLetIn (assignments, skletexpr) ->
    failwith "TODO : body with inner dependencies"
  | _ -> failhere __FILE__ "check_wf" "Bad toplevel expression form."

and check_wf_assignments (assignments : (fnLVar * fnExpr) list)
    (state : VarSet.t) =
  try
    List.iter
      (fun (v, e) ->
         if accepted_expression e
         then ()
         else
           failhere  __FILE__
             "check_wf_assignments"
             "Bad assignment, cannot discover variables.")
      assignments;
    true
  with Failure s -> false

and accepted_expression e =
  match e with
  | FnVar _
  | FnConst _ -> true
  | FnCond _ -> true
  | FnUnop (_, e') -> accepted_expression e'
  | FnBinop (_, e', e'') ->
    (accepted_expression e') && (accepted_expression e'')
  | _ -> false



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



(** Given a function an a set of state variables, return a mapping
    from state variable ids to the list of variable ids used in the
    function.
    @param stv A set of state variables.
    @input_func the function on which to compute the uses
    @return A mapping from state variable ids to lists of variable ids.
*)
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

    | FnLetExpr velist -> List.fold_left used_in_assignment map velist

    | _ -> failhere __FILE__ "uses"
             "Bad toplevel expr form, recursion should not have reached this."
  and used_in_assignment map (v, expr) =
    let var = var_of_fnvar v in
    if VarSet.mem var stv then update_map map var (f_expr expr) else map
  in
  aux_used_stvs stv input_func IM.empty

let rank_by_use stv uses_map =
  let num_uses_list =
    List.map
      (fun (vid, use_set) -> (vid, VarSet.cardinal use_set))
      (IM.bindings uses_map)
  in
  let ranked =
    List.sort
      (fun (_, use_num) (_, use_num')-> compare use_num use_num')
      num_uses_list
  in
  try
    List.map (fun (vid, _) -> VarSet.find_by_id stv vid) ranked
  with Not_found ->
    eprintf "[ERROR] Some undefined variable in rank_by_use.@.";
    raise (VariableDiscoveryError "rank_by_use")




let add_new_aux (ctx : context) aux_to_add aux_set =
  let same_expr_and_func =
    AuxSet.filter
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
  if AuxSet.cardinal same_expr_and_func > 0 then aux_set
  else
    begin
      printf "@.%s%s Adding new auxiliary :%s %s.@.Expression : %a.@.Function : %a@."
        (color "b-green") (color "black") color_default
        aux_to_add.avar.vname
        cp_fnexpr aux_to_add.aexpr cp_fnexpr aux_to_add.afunc;
      AuxSet.add aux_to_add aux_set
    end


(* TODO *)
let pick_best_recfunc fexpr_l =
  List.hd fexpr_l

let create_new_aux new_aux_vi expr =
  (* Adding auxiliaries in a smarter way. Since we cannot infer initial values
     now, there is an offset for the discovery. When the aux is supposed to
     accumulate constant values, this will create a problem. *)
  let rec_case = FnVar (FnVariable new_aux_vi) in
  let funcs =
    match expr with
    | FnBinop (op, expr1, expr2) when is_constant expr1 && is_constant expr2 ->
      [FnBinop (op, rec_case, expr2);
       FnBinop (op, expr1, rec_case);
       FnBinop (op, expr1, expr2)]
    | _ -> [rec_case]
  in
  let new_aux func =
    { avar = new_aux_vi;
      aexpr = expr;
      afunc = func;
      depends = VarSet.singleton new_aux_vi }
  in
  List.iter
    (fun func -> printf "Candidate auxiliary: %a.@." cp_fnexpr func)
    funcs;
  AuxSet.of_list (List.map new_aux funcs)


let function_updater xinfo xinfo_aux aux_set current_expr candidates aux_set' =
  let aux = AS.max_elt candidates in
  (* Create a new auxiliary to avoid deleting the old one *)
  let new_vi = mkFnVar (get_new_name ~base:!_aux_prefix_) (type_of aux.aexpr) in
  (**
     Replace the old expression of the auxiliary by the auxiliary. Be careful
     not to add too many recursive calls. Try to replace it only once, to avoid
     spurious recursive locations.
  *)
  let replace_aux =
    (replace_many
      aux.aexpr (FnVar (FnVariable new_vi))
      current_expr 1)
  in
  let cexpr =
    (** Replace auxiliary recurrence variables by their expression *)
    replace_available_vars xinfo xinfo_aux current_expr
  in
  (** Transform all a(i + ...) into a(i) if i + ... is the
      current index expression *)
  let new_f =
    pick_best_recfunc (List.map (reset_index_expressions xinfo) replace_aux)
  in
  let dependencies = used_in_fnexpr new_f in
  let new_auxiliary =
      { avar = new_vi; aexpr = cexpr;
        afunc = new_f; depends = dependencies}
  in
  if !debug then
    printf "@.Updated %s, now has accumulator : %a and expression %a@."
      new_vi.vname cp_fnexpr new_f cp_fnexpr cexpr;

  add_new_aux xinfo.context new_auxiliary aux_set'

(** Finding auxiliary variables given a map of state variables to expressions
    and the previous set of auxiliary variables.
    @param xinfo the execution info, for the state variables.
    @param xinfo_aux the execution info, for the auxliary variables.
    @param expr the expression of the state variables, normalized and at the
    current unfolding.
    @param aux_var_set auxiliary variables already created.
    @param aux_var_map map auxiliary variable id to its previous expression and
    associated function.
    @return A set of auxiliaries.
*)
let find_auxiliaries ?(not_last_iteration = true) i
    xinfo xinfo_aux expr (oset : AuxSet.t) input_expressions : AuxSet.t =

  let stv = xinfo.context.state_vars in

  let rec is_stv expr =
    match expr with
    | FnUnop (_, FnVar v)
    | FnVar v ->
      begin
        try
          VarSet.mem (check_option (vi_of v)) stv
        with Failure s -> false
      end
    | FnCond (c, e1, e2) -> is_stv c
    | _ -> false
  in

  let rec collect_stv expr =
    match expr with
    | FnUnop (_, FnVar v)
    | FnVar v -> v
    | FnCond (c, e1, e2) -> collect_stv c
    | _ -> failwith "Not an stv."
  in

  let is_candidate expr =
    match expr with
    | FnBinop (_, e1, e2)
    | FnCond (_, e1, e2) ->
      (** One of the operands must be a state variable
          but not the other *)
      (is_stv e1 && (not (fn_uses stv e2))) ||
      (is_stv e2 && (not (fn_uses stv e1)))
    (* Special rule for conditionals *)
    | _ ->  false
  in

  let handle_candidate f =
    function
    | FnBinop (_, e1, e2) ->
      begin
        match e1, e2 with
        | FnCond(c, _, _), estv when is_stv estv -> [collect_stv estv, c]
        | estv, FnCond(c, _, _) when is_stv estv -> [collect_stv estv, c]
        | e, estv  when is_stv estv -> [collect_stv estv, e]
        | estv, e when is_stv estv -> [collect_stv estv, e]
        | _ -> []
      end
    | FnCond (_, e1, e2) ->
      if is_stv e1 then [collect_stv e1, e2] else [collect_stv e1, e2]
    | _ ->  []
  in

  let candidates state e =
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
         in (ve, matching_candidates)::l)
      state []
  in

  (** Find in an auxliary set the auxilairies matching EXACTLY the expression *)
  let find_ce to_match auxset =
    AuxSet.filter (fun aux -> aux.aexpr @= to_match) auxset
  in

  (**  Returns a list of (vid, (e, f)) where (f,e) is built such that
       ce = g (e, ...) *)
  let find_subexpr top_expr emap =
    rec_expr
      (fun a b -> AuxSet.union a b) AuxSet.empty
      (fun e ->
         AuxSet.exists
           (fun aux -> aux.aexpr @= e) emap)
      (fun f e -> find_ce e emap)
      (fun c ->  AuxSet.empty) (fun v ->  AuxSet.empty)
      top_expr
  in

  (** Check that the function applied to the old expression gives
      the new expression. *)
  let match_increment aux_vs ne =
    AuxSet.filter
      (fun aux ->
         (** Exec expr, replace index variables by their expression and
             other variables by their expression.
         *)
         let fe', _ =
           unfold_expr {xinfo with
                      context = {xinfo.context with state_vars = VarSet.empty}}
             aux.afunc
         in

         (* Finish the work by replacing the auxiliary by its expression. *)
         let fe' =
           replace_expression
             (FnVar (FnVariable aux.avar)) aux.aexpr
             fe'
         in
         (* We keep the expressions such that applying the function associated
            to the auxiliary yields the current matched expression *)
         if !debug_dev then
           printf "Accumulation:@ @[%a@]@ %s==%s@ @[%a@] ? %s%B%s@."
             cp_fnexpr fe' (color "red") color_default cp_fnexpr ne
             (color "green") (fe' @= ne) color_default;
         fe' @= ne)
  in


  let update_one_candidate aux_set aux_set' candidate_expr =
    (** Replace subexpressions corresponding to state expressions
        in the candidate expression *)
    let current_expr =
      if i > 0 then
        IM.fold
          (fun vid e ce ->
             let vi = VarSet.find_by_id xinfo.context.state_vars vid in
             replace_AC
               xinfo_aux.context
               ~to_replace:(accumulated_subexpression vi e)
               ~by:(FnVar (FnVariable vi))
               ~ine:ce)
          xinfo_aux.state_exprs candidate_expr
      else
        candidate_expr
    in
    let current_expr =
      reduce_full ~limit:10
        (ctx_add_cexp xinfo_aux.context input_expressions)
        current_expr
    in
    (** If the expression is already "known", stop here *)
    match current_expr with
    | FnVar (FnVariable vi) ->
      if !debug then
        printf "@.Elim %a, we have it in %s@."
          cp_fnexpr current_expr vi.vname;
      (** No change to the auxiliary variable set *)
      aux_set'

    | _ ->
      begin
        match AuxSet.elements (find_ce current_expr aux_set) with
        | aux :: _ ->
          assert (aux.aexpr @= current_expr);
          (* The expression is exactly the expression of a aux *)
          AuxSet.add aux aux_set'

        | [] ->
          let sub_aux = find_subexpr current_expr aux_set in
          begin
            if AuxSet.cardinal sub_aux > 0
            then
              begin
                printf "@.%s%s Candidate increments some auxiliary.%s@."
                (color "black") (color "b-green") color_default;
              (* A subexpression of the expression is an auxiliary variable *)
              let corresponding_functions =
                match_increment aux_set current_expr sub_aux
              in
              begin
                if AS.cardinal corresponding_functions > 0
                then
                  let aux = AS.max_elt corresponding_functions in
                  if !debug then
                    printf "@.Variable %s is incremented by %a@."
                      aux.avar.vname cp_fnexpr aux.afunc;
                  let new_aux =
                    { aux with
                      aexpr =
                        replace_available_vars xinfo xinfo_aux current_expr } in
                  add_new_aux xinfo.context new_aux aux_set'


                else
                  (* We have to update the function *)
                if not_last_iteration then
                  function_updater xinfo xinfo_aux aux_set current_expr sub_aux aux_set'
                else
                  aux_set'
              end
              end
            else
              (* Check that the auxliary is not jsut an update by replacing
                 the current index expression *)
              let current_expr_i = reset_index_expressions xinfo current_expr in
              begin
                match AS.elements (find_ce current_expr_i aux_set) with
                | aux :: _ ->
                  if !debug then
                    printf "Variable is incremented after index update %s: %a@."
                      aux.avar.vname cp_fnexpr current_expr_i;
                  let new_aux = { aux with afunc = current_expr_i } in
                  add_new_aux xinfo.context new_aux aux_set'


                | _ ->
                  (* We have to create a new variable *)
                  if not_last_iteration then
                    let typ = type_of current_expr in
                    let new_aux_varinfo = mkFnVar (get_new_name ~base:!_aux_prefix_) typ in
                    let new_auxs =
                      create_new_aux new_aux_varinfo current_expr
                    in
                    if !debug then
                      printf "@.Adding new variable %s : %a@."
                        new_aux_varinfo.vname
                        cp_fnexpr current_expr;

                    AuxSet.fold
                      (fun new_aux rec_aux_set ->
                         add_new_aux xinfo.context new_aux rec_aux_set)
                      aux_set' new_auxs
                  else
                    aux_set'
              end
          end
      end
  in

  let update_aux aux_set aux_set' (stv, candidates) =
    if is_array_type stv.vtype then
      begin
        printf "Array %s : @.candidates: %a."
          stv.vname cp_expr_list candidates;
        failwith "TODO"
      end
    else
      List.fold_left (update_one_candidate aux_set)
        aux_set' candidates
  in

  let candidate_exprs = candidates xinfo.context.state_vars expr in
  if !debug then
    printf "Expression to create auxliaries :%a@."
      cp_fnexpr expr;
  List.fold_left (update_aux oset)
    AuxSet.empty candidate_exprs




(** Discover a set a auxiliary variables for a given variable.
    @param sketch the input problem representation.
    @param varid the id of the state variable that has to be analyzed.
    @return the new problem representation, with the update loop body
    and the updated state variables.
*)
let discover_for_id problem var =
  if !verbose then
    begin
      printf "[INFO] Discover for variable %s.@." var.vname;
      printf "       State: %a.@." VarSet.pp_var_names problem.scontext.state_vars
    end;
  aux_prefix var.vname;
  let idx_update = get_index_update problem in

  (** Fixpoint stops when the set of auxiliary variables is stable,
      which means the set of auxiliary variables and the associated functions
      do not change with new unfoldings.
  *)

  let rec fixpoint i (xinfo, oset : exec_info * AuxSet.t) =
    printf "@.%s%s%s%s@."
      (color "black") (color "b-blue")
      (pad ~c:'-' (fprintf str_formatter
                     "-------------------- UNFOLDING %i ----------------" i;
                  flush_str_formatter ()) 80)
      color_default;

    let xinfo', oset' =
      (** Reduce the depth of the state variables in the expression *)
      let expressions, inputs =
        let em, inp =
          unfold_once {xinfo with inputs = ES.empty} problem.main_loop_body
        in
        if !verbose then
        printf "[INFO] Unfolding result:@.@[<v 2>%s =@;%a@]@."
          var.vname cp_fnexpr (IM.find var.vid em);

        IM.map (reduction_with_warning xinfo.context) em, inp
      in
      if !verbose then
        printf "[INFO] Normalized:@.@[<v 2>%s =@;%a@]@."
          var.vname cp_fnexpr (IM.find var.vid expressions);

      (** Find the new set of auxiliaries by analyzing the expressions at the
          current unfolding level *)
      let oset' =
        find_auxiliaries i
          ~not_last_iteration:(i < !max_exec_no)
          xinfo                 (* Previous state. *)
          { xinfo with state_exprs = expressions} (* Current state. *)
          (IM.find var.vid expressions)             (* Expression analyzed. *)
          oset                         (* Current auxiliaries, current aux expressions. *)
          inputs
      in
      {xinfo with state_exprs = expressions;
                  index_exprs = unfold_index xinfo idx_update;
                  inputs = inputs },
      oset'
    in
    if (i > !max_exec_no - 1) || (same_aux oset oset')
    then
      xinfo', oset'
    else
      fixpoint (i + 1) (xinfo', oset')
  in


  let ctx = problem.scontext in
  discover_init ();

  printf "@.%s%s%s%s@."
    (color "black")
    (color "b-blue")
    (pad ~c:'-' (fprintf str_formatter
     "---------------- START UNFOLDINGS for %s ----------------"
       var.vname; flush_str_formatter ())
    80)
    color_default;

  let init_idx_exprs = create_symbol_map ctx.index_vars in
  (* Always start with the state variable symbols. *)
  let init_exprs = create_symbol_map ctx.state_vars in
  let init_i = { context = ctx;
                 state_exprs = init_exprs;
                 index_exprs = init_idx_exprs ;
                 inputs = ES.empty
               }
  in

  let _ , aux_set =
    fixpoint 0 (init_i, AuxSet.empty)
  in
  (* Filter out the auxiliaries that are just duplicates of a state variable. *)
  let clean_aux_set =
    remove_duplicate_auxiliaries init_i aux_set problem.main_loop_body
  in

  VarSet.iter discover_add (AuxSet.vars aux_set);
  (** Finally add the auxliaries at the beginning of the function. Since the
      auxliaries depend only on the inputs and not the value of the state
      variables we can safely add the assignments (or let bindings) at
      the beginning.
      Return the union of the new auxiliaries and the state variables.
  *)

  if !debug then
    begin
      printf "@.DISCOVER for variable %s finished.@." var.vname;
    end;
  printf "@.%sNEW VARIABLES :%s@." (color "b") color_default;
  AuxSet.iter
    (fun aux ->
       printf "@.(%i : %s) = (%a,@; %a)@." aux.avar.vid aux.avar.vname
         cp_fnexpr aux.aexpr cp_fnexpr aux.afunc
    ) clean_aux_set;

  let new_ctx, new_loop_body, new_constant_exprs =
    VUtils.compose init_i problem.main_loop_body clean_aux_set
  in
  discover_init ();
  {problem with scontext = new_ctx;
               main_loop_body = new_loop_body }



(** Main entry point.
    Discovers new variables that can be useful in parallelizing
    the computation.
    @param problem the problem representation.
    @param the modified problem representaiton, with new auxiliary variables.
*)

let timec = ref 0.0

let discover problem =
  if !verbose then printf "@.[INFO] Starting variable discovery...@.";

  let problem =
    if List.length problem.inner_functions > 0 then
      begin
        if !verbose then
          printf "@.[INFO] Preparing body, inlining inner loops.@.";
        InnerFuncs.inline_inner problem
      end
    else
      problem
  in
  timec := Unix.gettimeofday ();
  let stv = problem.scontext.state_vars in
  let ranked_stv =
    rank_by_use stv (uses stv  problem.main_loop_body)
  in
  (* For each variable, do the auxiliary variable discovery. *)
  let problem' =
    List.fold_left
      (fun problem var ->
         if is_array_type var.vtype || is_reinitialized problem var then
           (* Skip auxiliary discovery for array variables and variables that
              are reinitialized in the loop. *)
           (if !verbose then printf "[INFO] Skip %s.@." var.vname;
           problem)
         else
           discover_for_id problem var)
      problem
      ranked_stv
  in
  timec := Unix.gettimeofday () -. !timec;
  Format.printf "@.Variable discovery in %.3f s@." !timec;
  problem'
