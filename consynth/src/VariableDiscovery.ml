open Cil
open Utils
open Format
open SPretty
open ExpressionReduction
open SymbExe
open PpHelper
open VUtils
open Expressions
open SketchTypes

let debug = ref false
let debug_dev = ref true

let max_exec_no = ref 4

let discovered_aux = IH.create 10

let init () =
  IH.clear discovered_aux

(**
   Entry point : check that the function is a candidate for
    function discovery.
*)

let rec check_wf (input_function : T.sklet) (stv : VS.t) : T.sklet =
  match input_function with
  | T.SkLetExpr assignments ->
    input_function
  | T.SkLetIn (assignments, skletexpr) ->
    failwith "TODO : body with inner dependencies"

and check_wf_assignments (assignments : (T.skLVar * T.skExpr) list)
    (state : VS.t) =
  try
    List.iter
      (fun (v, e) ->
         if accepted_expression e
         then ()
         else raise (Failure "bad assgn")) assignments;
    true
  with Failure s -> false

and accepted_expression e =
  match e with
  | T.SkVar _
  | T.SkConst _ -> true
  | T.SkQuestion _ -> true
  | T.SkUnop (_, e') -> accepted_expression e'
  | T.SkBinop (_, e', e'') ->
    (accepted_expression e') && (accepted_expression e'')
  | _ -> false

(** Generation of new auxiliary variables *)
let allvars = ref VS.empty

let aux_var_prefix = ref "aux_"

let aux_var_counter = ref 0

let aux_init vs =
  allvars := vs;
  aux_var_counter := 0;
  aux_var_prefix :=
    (VS.fold
       (fun vi gen_prefix ->
          let prefix_contains = (vi.vname = gen_prefix)
          in
         if prefix_contains then
           (gen_prefix^vi.vname)
         else
           gen_prefix)
      vs
      !aux_var_prefix);;

let gen_fresh ty () =
  let fresh_name = (!aux_var_prefix)^(string_of_int (!aux_var_counter)) in
  incr aux_var_counter;
  match T.ciltyp_of_symb_type ty with
  | Some ct ->
    let fresh_var = makeVarinfo false fresh_name ct in
    allvars := VS.add fresh_var !allvars;
    fresh_var
  | None ->
    failwith "Failed in variable generation : couldn't find a variable type."


(** Rank the state variable according to sequential order assignment and then
    the number of incoming edges in the use-def graph.
*)
let merge_union vid ao bo =
  match ao, bo with
  | Some a, Some b -> Some (VS.union a b)
  | Some a, None -> Some a
  | _ , Some b -> Some b
  | _ ,_ -> None

let update_map map vi vi_used =
  if IM.mem vi.vid map then
    IM.add vi.vid (VS.union vi_used (IM.find vi.vid map)) map
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
  let rec aux_used_stvs stv inpt map =
    match inpt with
    | T.SkLetIn (velist, letin) ->
      let new_uses = List.fold_left used_in_assignment map velist in
      let letin_uses = aux_used_stvs stv letin IM.empty in
      IM.merge merge_union new_uses letin_uses
    | T.SkLetExpr velist -> List.fold_left used_in_assignment map velist

  and used_in_assignment map (v, expr) =
    (* Ignore assignment to 'state' it is only a terminal symbol in the
       function *)
    let vi =
      try
        check_option (T.vi_of v)
      with Failure s ->
        SError.exception_on_variable s v
    in
    let f_expr = T.rec_expr
        VS.union (* Join *)
        VS.empty (* Leaf *)
        (fun e -> false) (* No special cases *)
        (fun e -> VS.empty) (* Never used*)
        (fun c -> VS.empty) (* Handle constants *)
        (fun v ->
           VS.inter
             (VS.singleton (check_option (T.vi_of v))) stv) (* Variables *)
    in
    update_map map vi (f_expr expr)
  in
  aux_used_stvs stv input_func IM.empty

let rank_by_use uses_map =
  let num_uses_list =
    List.map
      (fun (vi, use_set) -> (vi, VS.cardinal use_set))
      (IM.bindings uses_map)
  in
  List.sort
    (fun (vi, use_num) (vi', use_num')-> compare use_num use_num')
    num_uses_list

(** Create a mapping from variable ids to variable expressions to start the
    algorithm *)
let create_symbol_map vs=
  VS.fold
    (fun vi map -> IM.add vi.vid (T.SkVar (T.SkVarinfo vi)) map) vs IM.empty

let add_new_aux aux_to_add (aux_vs, aux_exprs) =
  let same_expr_and_func =
    IM.filter
      (fun varid aux ->
         let func = replace_expression
             ~in_subscripts:true
             ~to_replace:(SkVar (SkVarinfo aux.avarinfo))
             ~by:(SkVar (SkVarinfo aux_to_add.avarinfo))
             ~ine:aux.afunc
         in
         aux.aexpr @= aux_to_add.aexpr && func @= aux_to_add.afunc)
      aux_exprs
  in
  if IM.cardinal same_expr_and_func > 0 then (aux_vs, aux_exprs)
  else
    begin
      printf "@.Adding new auxiliary : %s.@.Expression : %a.@.Function : %a@."
        aux_to_add.avarinfo.vname
        pp_skexpr aux_to_add.aexpr pp_skexpr aux_to_add.afunc;
      (VS.add aux_to_add.avarinfo aux_vs,
       IM.add aux_to_add.avarinfo.vid aux_to_add aux_exprs)
    end

let function_updater xinfo xinfo_aux (aux_vs, aux_exprs)
    current_expr candidates (new_aux_vs, new_aux_exprs) =
  let vid, aux = List.nth candidates 0 in
  (* Create a new auxiliary to avoid deleting the old one *)
  let new_vi = gen_fresh (T.type_of aux.aexpr) () in
  (* Replace the old expression of the auxiliary by the auxiliary *)
  let replace_aux =
    T.replace_expression
      aux.aexpr (T.SkVar (T.SkVarinfo new_vi))
      current_expr
  in
  let cexpr =
    (** Replace auxiliary recurrence variables by their expression *)
    replace_available_vars xinfo xinfo_aux current_expr
  in
  (** Transform all a(i + ...) into a(i) if i + ... is the
      current index expression *)
  let new_f = reset_index_expressions xinfo replace_aux in
  let dependencies = used_in_skexpr new_f in
  let new_auxiliary =
      { avarinfo = new_vi; aexpr = cexpr;
        afunc = new_f; depends = dependencies}
  in
  if !debug then
    printf "@.Updated %s, now has accumulator : %a and expression %a@."
      new_vi.vname pp_skexpr new_f pp_skexpr cexpr;

  add_new_aux new_auxiliary (new_aux_vs, new_aux_exprs)

(** Finding auxiliary variables given a map of state variables to expressions
    and the previous set of auxiliary variables.
    @param id the state variable we are analyzing.
    @param stv the state variables.
    @param exprs the current expressions of the state variables.
    @param aux_var_set auxiliary variables already created.
    @param aux_var_map map auxiliary variable id to its previous expression and
    associated function.
    @return the pair of state variables and mapping from ids to the pair of
    expression and function.
*)
let find_auxiliaries ?(not_last_iteration = true) i
    xinfo xinfo_aux expr
    (aux_var_set, aux_var_map) input_expressions =
  let stv = xinfo.context.state_vars in
  let rec is_stv =
    function
    | T.SkUnop (_, T.SkVar v)
    | T.SkVar v ->
      begin
        try
          VS.mem (check_option (T.vi_of v)) stv
        with Failure s -> false
      end
    | T.SkQuestion (c, e1, e2) -> is_stv c
    | _ -> false
  in
  let is_candidate expr =
    match expr with
    | T.SkBinop (_, e1, e2)
    | T.SkQuestion (_, e1, e2) ->
      (** One of the operands must be a state variable
          but not the other *)
      (is_stv e1 && (not (T.sk_uses stv e2))) ||
      (is_stv e2 && (not (T.sk_uses stv e1)))
    (* Special rule for conditionals *)
    | _ ->  false
  in
  let handle_candidate =
    function
    | T.SkBinop (_, e1, e2) ->
      begin
        match e1, e2 with
        | SkQuestion(c, _, _), estv when is_stv estv -> [c]
        | estv, SkQuestion(c, _, _) when is_stv estv -> [c]
        | e, estv  when is_stv estv -> [e]
        | estv, e when is_stv estv -> [e]
        | _ -> []
      end
    | T.SkQuestion (_, e1, e2) ->
      if is_stv e1 then [e2] else [e1]
    | _ ->  []
  in
  let candidates e =
    T.rec_expr
      (fun a b -> a@b)
      []
      is_candidate
      handle_candidate
      (fun c -> [])
      (fun v -> [])
      e
  in
  (** Find in a expression map the bindings matching EXACTLY the expression *)
  let find_ce to_match emap =
    let cemap = IM.filter (fun vid aux -> aux.aexpr @= to_match) emap in
    IM.bindings cemap
  in
  (**  Returns a list of (vid, (e, f)) where (f,e) is built such that
       ce = g (e, ...) *)
  let find_subexpr top_expr emap =
    T.rec_expr
      (fun a b -> a@b) []
      (fun e ->
         IM.exists
           (fun vid aux -> aux.aexpr @= e) emap)
      (fun e -> find_ce e emap)
      (fun c -> []) (fun v -> [])
      top_expr
  in
  (** Check that the function applied to the old expression gives
      the new expression. *)
  let match_increment aux_vs ne =
    List.filter
      (fun (vid, aux) ->
         (** Exec expr, replace index variables by their expression and
             other variables by their expression.
         *)
         let fe', _ =
           exec_expr {xinfo with
                      context = {xinfo.context with state_vars = VS.empty}}
             aux.afunc
         in

         (* Finish the work by replacing the auxiliary by its expression. *)
         let fe' =
           T.replace_expression
             (T.SkVar (T.SkVarinfo aux.avarinfo)) aux.aexpr
             fe'
         in
         (* We keep the expressions such that applying the function associated
            to the auxiliary yields the current matched expression *)
         if !debug_dev then
           printf "Increment %a == %a ? %B@."
             pp_skexpr fe' pp_skexpr ne (fe' @= ne);
         fe' @= ne)
  in
  let update_aux (aux_vs, aux_exprs) (new_aux_vs, new_aux_exprs)
      candidate_expr =
    (** Replace subexpressions by their auxliiary *)
    if !debug then
      printf "@.Candidate : %a@." pp_skexpr candidate_expr;
    (** Replace subexpressions corresponding to state expressions
        in the candidate expression *)
    let current_expr =
      if i > 0 then
        IM.fold
          (fun vid e ce ->
             let vi = VSOps.find_by_id vid xinfo.context.state_vars in
             replace_AC
               xinfo_aux.context
               ~to_replace:(accumulated_subexpression vi e)
               ~by:(T.SkVar (T.SkVarinfo vi))
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
    | T.SkVar (T.SkVarinfo vi) ->
      if !debug then
        printf "@.Elim %a, we have it in %s@."
          pp_skexpr current_expr vi.vname;
      (** No change to the auxiliary variable set *)
      (new_aux_vs, new_aux_exprs)

    | _ ->
      begin
        match find_ce current_expr aux_exprs with
        (* TODO : how do we choose which expression to use in this
           case ? Now only pick the first expression to come.
        *)
        | (vid, aux):: _ ->
          assert (aux.aexpr @= current_expr);
          (* The expression is exactly the expression of a aux *)
          let vi = VSOps.find_by_id vid aux_vs in
          (VS.add vi new_aux_vs,
           IM.add vid aux new_aux_exprs)

        | [] ->
          let ef_list = find_subexpr current_expr aux_exprs in
          begin
            if List.length ef_list > 0
            then
              begin
              printf "@.Candidate increments some auxiliary.@.";
              (* A subexpression of the expression is an auxiliary variable *)
              let corresponding_functions =
                match_increment aux_vs current_expr ef_list
              in
              begin
                if List.length corresponding_functions > 0
                then
                  let vid, aux = List.nth corresponding_functions 0 in
                  if !debug then
                    printf "@.Variable %s is incremented by %a@."
                      aux.avarinfo.vname pp_skexpr aux.afunc;
                  let new_aux =
                    { aux with
                      aexpr =
                        replace_available_vars xinfo xinfo_aux current_expr } in
                  add_new_aux new_aux (new_aux_vs, new_aux_exprs)


                else
                  (* We have to update the function *)
                if not_last_iteration then
                  function_updater xinfo xinfo_aux
                    (aux_vs, aux_exprs)
                    current_expr ef_list (new_aux_vs, new_aux_exprs)
                else
                  (new_aux_vs, new_aux_exprs)
              end
              end
            else
              (* Check that the auxliary is not jsut an update by replacing
                 the current index expression *)
              let current_expr_i = reset_index_expressions xinfo current_expr in
              begin
                match find_ce current_expr_i aux_exprs with
                | (vid, aux) :: _ ->
                  if !debug then
                    printf "Variable is incremented after index update %s: %a@."
                      aux.avarinfo.vname pp_skexpr current_expr_i;
                  let new_aux = { aux with afunc = current_expr_i } in
                  add_new_aux new_aux (new_aux_vs, new_aux_exprs)


                | _ ->
                  (* We have to create a new variable *)
                  if not_last_iteration then
                    let typ = T.type_of current_expr in
                    let new_aux_varinfo = gen_fresh typ () in
                    let new_aux =
                        { avarinfo = new_aux_varinfo;
                          aexpr = current_expr;
                          afunc = T.SkVar (T.SkVarinfo new_aux_varinfo);
                          depends = VS.singleton new_aux_varinfo }
                    in
                    if !debug then
                      printf "@.Adding new variable %s : %a@."
                        new_aux_varinfo.vname
                        pp_skexpr current_expr;

                    add_new_aux new_aux (new_aux_vs, new_aux_exprs)
                  else
                    (new_aux_vs, new_aux_exprs)
              end
          end
      end
  in
  let candidate_exprs = candidates expr in
  if !debug then
    printf "Expression to create auxliaries :%a@."
      pp_skexpr expr;
  List.fold_left (update_aux (aux_var_set, aux_var_map))
    (VS.empty, IM.empty) candidate_exprs

(** Discover a set a auxiliary variables for a given variable.
    @param stv the set of state variables.
    @param idx the set of index variables.
    @param input_func the input function.
    @param varid the id of the variable we're analyzing.
    @return a pair of auxiliary variables and auxiliary functions.
*)
let discover_for_id ctx idx_update input_func varid =
  GenVars.init ();
  init ();
  (*  max_exec_no := VS.cardinal stv + 1; *)
  let init_idx_exprs = create_symbol_map ctx.index_vars in
  let init_exprs = create_symbol_map ctx.state_vars in
  let init_i = { context = ctx;
                 state_exprs = init_exprs;
                 index_exprs = init_idx_exprs ;
                 inputs = T.ES.empty
               }
  in
  (** Fixpoint stops when the set of auxiliary varaibles is stable,
      which means the set of auxiliary variables hasn't changed and
      the functions associated to these auxilary variables haven't
      changed.
  *)
  let rec fixpoint i xinfo aux_var_set aux_var_map =
    if !debug then Format.printf "@.---Unrolling %i---@."i else ();
    let new_xinfo, (new_var_set, new_aux_exprs) =
      (** Find the new expressions by expanding once. *)
      let exprs_map, input_expressions =
        exec_once {xinfo with inputs = T.ES.empty} input_func
      in
      (** Reduce the depth of the state variables in the expression *)
      let new_exprs =
        IM.map
          (reduction_with_warning xinfo.context)
          exprs_map
      in
      (** Compute the new expressions for the index *)
      let xinfo_index = { context =
                            { state_vars = xinfo.context.index_vars ;
                              index_vars = VS.empty;
                              all_vars = VS.empty;
                              costly_exprs = ES.empty;};
                          state_exprs = xinfo.index_exprs ;
                          index_exprs = IM.empty ;
                          inputs = T.ES.empty;
                        }
      in
      let new_idx_exprs =
        let full_map, _ = exec_once ~silent:true xinfo_index idx_update in
        VS.fold
          (fun vi map -> IM.add vi.Cil.vid (IM.find vi.vid full_map) map)
          xinfo.context.index_vars IM.empty
      in
      (** Find the new set of auxliaries by analyzing the expressions at the
          current expansion level *)
      let xinfo' = { xinfo with state_exprs = new_exprs} in
      let aux_var_set, aux_var_map =
        find_auxiliaries i
          ~not_last_iteration:(i < !max_exec_no)
          xinfo xinfo'
          (IM.find varid new_exprs)
          (aux_var_set, aux_var_map)
          input_expressions
      in
      (**
         Generate the new information for the next iteration and the set
          of auxilaries with their expressions at the current expansion
      *)

      {xinfo with state_exprs = new_exprs;
                  index_exprs = new_idx_exprs;
                  inputs = input_expressions },
      (aux_var_set, aux_var_map)
    in
    (** WIP To avoid non-termination simply use a limit, can find better
        solution *)
    printf "@.--------------------@.";
    if (i > !max_exec_no - 1) || (same_aux aux_var_map new_aux_exprs)
    then
      new_xinfo, (new_var_set, new_aux_exprs)
    else
      fixpoint (i + 1) new_xinfo new_var_set new_aux_exprs
  in

  let _ , (aux_vs, aux_ef) =
    fixpoint 0 init_i VS.empty IM.empty
  in
  (* Filter out the auxiliaries that are just duplicates of a state variable. *)
  let clean_aux, clean_aux_ef =
    remove_duplicate_auxiliaries init_i (aux_vs, aux_ef) input_func
  in

  VS.iter (fun vi -> IH.add discovered_aux vi.Cil.vid vi) aux_vs;
  (** Finally add the auxliaries at the beginning of the function. Since the
      auxliaries depend only on the inputs and not the value of the state
      variables we can safely add the assignments (or let bindings) at
      the beginning.
      Return the union of the new auxiliaries and the state variables.
  *)

  (** Remove redundant auxiliaries : auxiliaries that have the same expressions
      as state variables *)
  if !debug then
    begin
      printf "@.DISCOVER for variable %s finished.@."
        (VSOps.find_by_id varid ctx.state_vars).vname;
    end;
  printf "@.NEW VARIABLES :@.";
  VS.iter
    (fun vi ->
       printf "@.(%i : %s) = (%a,@; %a)@." vi.C.vid vi.C.vname
         pp_skexpr (IM.find vi.C.vid clean_aux_ef).aexpr
         pp_skexpr (IM.find vi.C.vid clean_aux_ef).afunc
    ) clean_aux;

  VUtils.compose init_i input_func clean_aux clean_aux_ef



(** Main entry point.
    Discovers new variables that can be useful in parallelizing
    the computation.
    @param stv the set of state variables.
    @param input_func the input function of the algorithm.
    @param igu the init, guard and update statements of the enclosing loop. It
    will be used in computing the symbolic index in the algorithm.
    @return A new set of state variables and a new function with the variables
    discovered by the algortihm.
*)

let timec = ref 0.0

let discover ctx u input_func =
  timec := Unix.gettimeofday ();
  T.create_boundary_variables ctx.index_vars;

  aux_init (VS.union ctx.state_vars ctx.index_vars);
  (** Analyze the index and produce the update function for
      the index.
  *)
  let ranked_stv = rank_by_use (uses ctx.state_vars input_func) in
  let final_stv, final_func =
    List.fold_left
      (fun (new_stv, new_func)  (vid, _) ->
         discover_for_id
           (ctx_update_vsets ctx new_stv)
             u new_func vid)
      (ctx.state_vars, input_func)
      ranked_stv
  in
  timec := Unix.gettimeofday () -. !timec;
  Format.printf "@.Variable discovery in %.3f s@." !timec;
  final_stv, final_func
