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
open Fn
open Format
open FnPretty
open SymbExe
open Utils
open VUtils

module ER = ExpressionReduction
module RFind = RecurrenceFinder

open PpTools

exception VariableDiscoveryError of string

let debug = ref false
let verbose = ref false
let debug_dev = ref true


let max_exec_no =
  ref (Conf.get_conf_int "variable_discovery_max_unfoldings")

let symbex_inner_loop_width = ref 3

let unfold_index xinfo idx_update =
  let ix =
    { context =
        { state_vars = xinfo.context.index_vars ;
          index_vars = VarSet.empty;
          used_vars = VarSet.empty;
          all_vars = VarSet.empty;
          costly_exprs = ES.empty;};
      state_exprs = xinfo.index_exprs ;
      intermediate_states = IM.empty;
      index_exprs = IM.empty ;
      inputs = ES.empty;
    }
  in
  let idx = VarSet.max_elt xinfo.context.index_vars in
  let idx_u = wrap_state [FnVariable idx, idx_update] in
  let ix' = unfold_once ~silent:true ix idx_u in
  VarSet.fold
    (fun vi map -> IM.add vi.vid (IM.find vi.vid ix'.state_exprs) map)
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
  | FnRecord (vs, emap) ->
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




(** Adding auxiliaries in a smarter way. Since we cannot infer initial values
     now, there is an offset for the discovery. When the aux is supposed to
     accumulate constant values, this will create a problem.
*)
let create_new_aux
    (xinfo : exec_info)
    (xinfo_aux : exec_info)
    (new_aux : fnV)
    (expr : fnExpr) : AuxSet.t =
  let rec_case = FnVariable new_aux in
  let funcs  = RFind.get_base_accus xinfo.context rec_case expr in
  let new_aux (func, t) =
    { avar = new_aux;
      aexpr = replace_available_vars xinfo xinfo_aux expr;
      afunc = func;
      atype = t;
      depends = VarSet.singleton new_aux }
  in
  AuxSet.of_list (List.map new_aux funcs)



(**
   Returns an expression where expr has been replaced by var in expr'. The
   purpose is to use the result of this to build a recursive function (an
   accumulator).
   @param: var the variable that acts as the recursion location.
   @param: expr the expression of the auxiliary in the previous unfolding.
   @param: expr' the expression from which to deduce the recursion.
*)

let update_with_one_candidate
    ((i, ni) : int * bool)
    (xinfo : exec_info)
    (xinfo_out : exec_info)
    (aux_set : AuxSet.t)
    (aux_set': AuxSet.t)
    (candidate_expr : fnExpr) : AuxSet.t =

  let new_aux_case cexpr aset aset' =
    if ni then
      let typ = type_of cexpr in
      let new_aux_varinfo = mkFnVar (get_new_name ~base:!RFind._aux_prefix_) typ in
      let new_auxs = create_new_aux xinfo xinfo_out new_aux_varinfo cexpr in

      if !debug then
        printf "@.Adding new variable %s@;with expression@;%a@."
          new_aux_varinfo.vname
          cp_fnexpr cexpr;

      AuxSet.fold
        (fun aux new_auxs ->
           AuxSet.add_new_aux xinfo.context new_auxs aux)
        new_auxs
        aset'
    else begin
      if !verbose then printf "[INFO] Skipped adding new variable.@.";
      aset'
    end
  in

  let index_update_case aux candidate_i =
    if !debug then
      printf "Variable is incremented after index update %s: %a@."
        aux.avar.vname cp_fnexpr candidate_i;
    let new_aux = { aux with afunc = candidate_i } in
    AuxSet.add_new_aux xinfo.context aux_set' new_aux
  in

  let accumulation_case candidate possible_accs aux_set' =
    let aux = AS.max_elt possible_accs in
    if !debug then
      printf "@.Variable %s is incremented by %a@."
        aux.avar.vname cp_fnexpr aux.afunc;
    let new_aux =
      { aux with
        aexpr =
          replace_available_vars xinfo xinfo_out candidate } in
    AuxSet.add_new_aux xinfo.context aux_set' new_aux
  in

  (** Replace subexpressions corresponding to state expressions
      in the candidate expression *)
  let candidate_expr', e =
    let e = find_computed_expressions i xinfo xinfo_out candidate_expr in
    (ER.normalize
       (ctx_add_cexp xinfo_out.context xinfo_out.inputs)) e, e
  in

  if !verbose then
    (printf "@.[INFO] ===== NEW CANDIDATE =====@.";
     printf "@[<v 4>[INFO] Candidate expr:@;%a@]@." cp_fnexpr candidate_expr');

  match candidate_expr' with
  | FnVar (FnVariable vi) ->
    if !debug then
      printf "@.Elim %a, we have it in %s@."
        cp_fnexpr candidate_expr' vi.vname;
    aux_set'

  | _ ->
    begin
      match AuxSet.elements (find_matching_aux candidate_expr' aux_set) with
      | aux :: _ ->
        assert (aux.aexpr @= candidate_expr');
        (* The expression is exactly the expression of a aux *)
        if !verbose then printf "[INFO] No change to auxiliary.@.";
        AuxSet.add aux aux_set'

      | [] ->
        let sub_aux = find_subexpr candidate_expr' aux_set in
        begin
          if AuxSet.cardinal sub_aux > 0
          then
            begin
              printf "@.%s%s Candidate increments some auxiliary.%s@."
                (color "black") (color "b-green") color_default;
              if !verbose then
                printf "@[<v 4>[INFO] Increments auxiliaries:@;%a.@]@."
                  AuxSet.pp_aux_set sub_aux;
              (* A subexpression of the expression is an auxiliary variable *)
              let possible_accs = RFind.find_accumulator xinfo candidate_expr' sub_aux in
              if AS.cardinal possible_accs > 0
              then
                accumulation_case candidate_expr' possible_accs aux_set'
              else if ni then
                RFind.update_accumulator xinfo xinfo_out candidate_expr' sub_aux aux_set'
              else
                aux_set'
            end
          else
            (* Check that the auxliary is not jsut an update by replacing
               the current index expression *)
            let candidate_i = reset_index_expressions xinfo candidate_expr' in
            begin
              match AS.elements (find_matching_aux candidate_i aux_set) with
              | aux :: _ -> index_update_case aux candidate_i
              | _ -> new_aux_case candidate_expr' aux_set aux_set'
            end
        end
    end


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
    xinfo_in xinfo_out expr (oset : AuxSet.t) : AuxSet.t =
  let aux_one_candidate =
    update_with_one_candidate
      (i, not_last_iteration)
      xinfo_in xinfo_out
  in

  let update_aux aux_set aux_set' (stv, candidates) =
    if is_array_type stv.vtype &&
       List.length candidates = !symbex_inner_loop_width
    then
      (aux_one_candidate aux_set) aux_set' (FnVector candidates)
    else
      List.fold_left (aux_one_candidate aux_set) aux_set' candidates
  in

  let candidate_exprs = candidates xinfo_in.context.state_vars expr in
  if !debug then
    printf "@[<v 4>[DEBUG] Expression to create auxiliaries from:@;%a@]@."
      cp_fnexpr expr;
  List.fold_left (update_aux oset) AuxSet.empty candidate_exprs



let rec fixpoint problem var i (xinfo, oset : exec_info * AuxSet.t) =
  let idx_update = get_index_update problem in
  printf "@.%s%s%s%s@."
    (color "black") (color "b-blue")
    (pad ~c:'-' (fprintf str_formatter
                   "-------------------- UNFOLDING %i ----------------" i;
                 flush_str_formatter ()) 80)
    color_default;

  let xinfo', oset' =
    (** Reduce the depth of the state variables in the expression *)
    let xinfo1 =
      let xinfo0 =
        unfold_once {xinfo with inputs = ES.empty} problem.main_loop_body
      in
      if !verbose then
        printf "[INFO] Unfolding result:@.@[<v 2>%s =@;%a@]@."
          var.vname cp_fnexpr (IM.find var.vid xinfo0.state_exprs);
      {
        xinfo0 with
        state_exprs =
          IM.map (ER.normalize xinfo.context --> enormalize xinfo.context)
            xinfo0.state_exprs
      }
    in
    if !verbose then
      printf "[INFO] Normalized:@.@[<v 2>%s =@;%a@]@."
        var.vname cp_fnexpr (IM.find var.vid xinfo1.state_exprs);

    (** Find the new set of auxiliaries by analyzing the expressions at the
        current unfolding level *)
    let oset' =
      find_auxiliaries i
        ~not_last_iteration:(i < !max_exec_no)
        xinfo
        xinfo1
        (IM.find var.vid xinfo1.state_exprs)
        oset
    in
    {xinfo1 with
     index_exprs = unfold_index xinfo1 idx_update},
    oset'
  in
  if (i > !max_exec_no - 1) || (same_aux oset oset')
  then
    xinfo', oset'
  else
    fixpoint problem var (i + 1) (xinfo', oset')



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
      printf "       State: %a.@." VarSet.pp_var_names problem.scontext.state_vars;
      printf "       Function: %a.@." pp_fnexpr problem.main_loop_body;
    end;
  RFind.aux_prefix var.vname;

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

  let start_exec_state =
    {
      context = ctx;
      state_exprs = create_symbol_map ctx.state_vars;
      index_exprs = create_symbol_map ctx.index_vars;
      intermediate_states = IM.empty;
      inputs = ES.empty
    }
  in
  let _ , aux_set =
    fixpoint problem var 0 (start_exec_state, AuxSet.empty)
  in
  (* Filter out the auxiliaries that are just duplicates of a state variable. *)
  let clean_aux_set =
    remove_duplicate_auxiliaries start_exec_state aux_set problem.main_loop_body
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
  printf "@.@[<v 4>%sNEW VARIABLES :%s%a@]@."
    (color "b") color_default
    (fun fmt a ->
       AuxSet.iter
         (fun aux ->
            printf "@.(%i : %s) = %a@." aux.avar.vid aux.avar.vname
              cp_fnexpr aux.afunc) a)
    clean_aux_set;

  let problem' = VUtils.compose problem start_exec_state clean_aux_set in
  discover_init ();
  problem'


(** Main entry point.
    Discovers new variables that can be useful in parallelizing
    the computation.
    @param problem the problem representation.
    @param the modified problem representaiton, with new auxiliary variables.
*)

let timec = ref 0.0

let discover problem =
  if !verbose then printf "@.[INFO] Starting variable discovery...@.";

  let prepare pb =
    if List.length pb.inner_functions > 0 then
      begin
        if !verbose then
          printf "@.[INFO] Preparing body, inlining inner loops.@.";
        InnerFuncs.inline_inner !symbex_inner_loop_width pb
      end
    else
      pb
  in
  timec := Unix.gettimeofday ();
  let stv = problem.scontext.state_vars in
  let ranked_stv =
    rank_by_use stv (FnDep.collect_dependencies problem.scontext problem.main_loop_body)
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
           discover_for_id (prepare problem) var)
      problem
      ranked_stv
  in
  timec := Unix.gettimeofday () -. !timec;
  Format.printf "@.Variable discovery in %.3f s@." !timec;
  problem'
