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
  let ix' = unfold_once ~silent:true ix idx_update in
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




let pick_best_recfunc fexpr_l =
  List.hd fexpr_l


(** Adding auxiliaries in a smarter way. Since we cannot infer initial values
     now, there is an offset for the discovery. When the aux is supposed to
     accumulate constant values, this will create a problem.
*)
let create_new_aux new_aux_vi expr =
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
  AuxSet.of_list (List.map new_aux funcs)


(**
   Returns an expression where expr has been replaced by var in expr'. The
   purpose is to use the result of this to build a recursive function (an
   accumulator).
   @param: var the variable that acts as the recursion location.
   @param: expr the expression of the auxiliary in the previous unfolding.
   @param: expr' the expression from which to deduce the recursion.
*)
let make_rec_calls
    (var, aux_expr : fnV * fnExpr) (expr' : fnExpr) : fnExpr list =
  match aux_expr, expr' with
  | FnVector el, FnVector el' ->
    assert (List.length el = List.length el');
    let make_cell_rec_call j e =
      let ej =
        replace_many_AC e (mkVarExpr ~offsets:[FnConst (CInt j)] var) (el' >> j) 1
      in
      match ej with
      | hd :: tl -> hd
      | [] ->
        failhere __FILE__ "make_rec_calls" "Unexpected empty recursion locs."
    in
    [FnVector(List.mapi make_cell_rec_call el)]

  | _, _ -> replace_many aux_expr (mkVarExpr var) expr' 1

let update_accu
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
    let replace_aux = make_rec_calls (new_vi, candidate_aux.aexpr) expr in
    let new_f =
      pick_best_recfunc (List.map (reset_index_expressions xinfo) replace_aux)
    in

    let new_auxiliary =
      {
        avar = new_vi;
        aexpr = replace_available_vars xinfo xinfo_aux expr;
        afunc = new_f;
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
      let new_aux_varinfo = mkFnVar (get_new_name ~base:!_aux_prefix_) typ in
      let new_auxs = create_new_aux new_aux_varinfo cexpr in

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
     (reduce_full ~limit:i
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
              let possible_accs = find_accumulator xinfo candidate_expr' sub_aux in
              if AS.cardinal possible_accs > 0
              then
                accumulation_case candidate_expr' possible_accs aux_set'
              else if ni then
                update_accu xinfo xinfo_out candidate_expr' sub_aux aux_set'
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
         IM.map (reduction_with_warning xinfo.context) xinfo0.state_exprs
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
      printf "       State: %a.@." VarSet.pp_var_names problem.scontext.state_vars
    end;
  aux_prefix var.vname;

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
  printf "@.%sNEW VARIABLES :%s@." (color "b") color_default;
  AuxSet.iter
    (fun aux ->
       printf "@.(%i : %s) = %a@." aux.avar.vid aux.avar.vname
         cp_fnexpr aux.afunc)
    clean_aux_set;

  let new_ctx, new_loop_body, new_constant_exprs =
    VUtils.compose start_exec_state problem.main_loop_body clean_aux_set
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
        InnerFuncs.inline_inner !symbex_inner_loop_width problem
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
