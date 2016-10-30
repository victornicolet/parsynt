open Cil
open Utils
open Format
open SPretty
open ExpressionReduction
open SymbExe

module T = SketchTypes

let debug = ref false

let max_exec_no = ref 3

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
    (state : VS.t)=
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

let aux_var_prefix = ref "x_"

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
    if v = T.SkState then IM.empty
    else
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


let function_updater xinfo (aux_vs, aux_exprs)
    current_expr candidates (new_aux_vs, new_aux_exprs) =
  let vid, (e, _) = List.nth candidates 0 in
  let vi = VSOps.find_by_id vid aux_vs in
  (* Replace the old expression of the auxiliary by the auxiliary *)
  let replace_aux =
    T.replace_expression
      e (T.SkVar (T.SkVarinfo (VSOps.find_by_id vid aux_vs)))
      current_expr
  in

  let new_f =
    IM.fold
      (fun idx_id idx_expr e ->
         try
           (* Replace the index expressions by the index itself *)
           T.replace_expression ~in_subscripts:true
             idx_expr
             (T.SkVar
                (T.SkVarinfo
                   (VSOps.find_by_id idx_id xinfo.index_set))) e
         with Not_found ->
           Format.eprintf "@.Index with id %i not found in %a.@."
             idx_id VSOps.pvs xinfo.index_set;
           raise Not_found
      )
      xinfo.index_exprs
      replace_aux
  in

  let updated_exprs = IM.add vid (current_expr, new_f) new_aux_exprs in

  (VS.add vi new_aux_vs, updated_exprs)

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
let find_auxiliaries xinfo expr (aux_var_set, aux_var_map) input_expressions =
  let stv = xinfo.state_set in
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

    | _ ->  false
  in
  let handle_candidate =
    function
    | T.SkBinop (_, e1, e2)
    | T.SkQuestion (_, e1, e2) ->
      if is_stv e1 then [e2] else [e1]
    | _ ->  []
  in
  let candidates e =
    T.rec_expr
      (fun a b -> a@b)
      []
      (fun e ->
         let v = is_candidate e in
         if !debug && v
         then printf "Candidate : %a@." pp_skexpr e else ();
         v)
      handle_candidate
      (fun c -> [])
      (fun v -> [])
      e
  in
  (** Find in a expression map the bindings matching EXACTLY the expression *)
  let find_ce to_match emap =
    let cemap = IM.filter (fun vid (auxe, f) -> auxe = to_match) emap in
    IM.bindings cemap
  in
  (**  Returns a list of (vid, (e, f)) where (f,e) is built such that
       ce = g (e, ...) *)
  let find_subexpr top_expr emap =
    T.rec_expr
      (fun a b -> a@b) []
      (fun e -> IM.exists (fun vid (auxe, f) -> auxe = e) emap)
      (fun e -> find_ce e emap)
      (fun c -> []) (fun v -> [])
      top_expr
  in
  (** Check that the function applied to the old expression gives
      the new expression. *)
  let match_increment aux_vs ne =
    List.filter
      (fun (vid, (e, fe)) ->
         (** Exec expr, replace index variables by their expression and
             other variables by their expression.
         *)
         let fe', _ = exec_expr xinfo fe in
         (* Finish the work by replacing the auxiliary by its expression. *)
         let fe' =
           T.replace_expression
             (T.SkVar (T.SkVarinfo (VSOps.find_by_id vid aux_vs))) e
             fe'
         in
         (* We keep the expressions such that applying the function associated
            to the auxiliary yields the current matched expression *)
         if !debug then
           printf "@.Matching increment : (%a == %a) = %B@."
             pp_skexpr fe' pp_skexpr ne (fe' = ne);
         (** TODO : equality under commutatitivty and associativity *)
         fe' = ne)
  in
  let update_aux (aux_vs, aux_exprs) (new_aux_vs, new_aux_exprs) cexpr =
    let current_expr =
      reduce_full ~limit:10 VS.empty input_expressions cexpr
    in
    if !debug then
      Format.fprintf Format.std_formatter
        "Lifting inputs transforms @.%a@.to@.%a@."
        pp_skexpr current_expr pp_skexpr current_expr
    else ();
    match find_ce current_expr aux_exprs with
    (* TODO : how do we choose which expression to use in this
       case ? Now only pick the first expression to come.
    *)
    | (vid, (e,f)):: _ ->
      assert (e = current_expr);
      (* The expression is exactly the expression of a aux *)
      let vi = VSOps.find_by_id vid aux_vs in
      (VS.add vi new_aux_vs,
       IM.add vid (e, T.SkVar (T.SkVarinfo vi)) new_aux_exprs)

    | [] ->
      let ef_list = find_subexpr current_expr aux_exprs in
      begin
        if List.length ef_list > 0
        then
          (* A subexpression of the expression is an auxiliary variable *)
          let corresponding_functions =
            match_increment aux_vs current_expr ef_list
          in
          begin
            if List.length corresponding_functions > 0
            then
              let vid, (e, f) = List.nth corresponding_functions 0 in
              let vi = VSOps.find_by_id vid aux_vs in

              (VS.add vi new_aux_vs, IM.add vid (current_expr, f) new_aux_exprs)


            else
              (* We have to update the function *)
              function_updater xinfo (aux_vs, aux_exprs)
                current_expr ef_list (new_aux_vs, new_aux_exprs)
          end
        else
          (* We have to create a new variable *)
          let typ = T.type_of current_expr in
          let new_aux = gen_fresh typ () in
          let updated_aux = VS.add new_aux new_aux_vs in
          let updated_exprs =
            IM.add
              new_aux.vid
              (current_expr, T.SkVar (T.SkVarinfo new_aux))
              new_aux_exprs
          in
          (updated_aux, updated_exprs)
      end
  in

  List.fold_left (update_aux (aux_var_set, aux_var_map))
    (VS.empty, IM.empty) (candidates expr)

(** Given a set of auxiliary variables and the associated functions,
    and the set of state variable and a function, return a new set
    of state variables and a function.
*)
let compose xinfo f aux_vs aux_ef =
  let new_stv = VS.union xinfo.state_set aux_vs in
  let new_func =
    T.compose_head
      (IM.fold
         (fun aux_vid (e, f) assgn_list ->
            (** Distinguish different cases :
                - the function is not identity but an accumulator, we add the
                function 'as is' in the loop body.
                TODO : graph analysis to place the let-binding at the right
                position.
                - the function f is the identity, then the auxliary variable
                depends on a finite prefix of the inputs. The expression depends
                on the starting index
            *)
            match f with
            | T.SkVar (T.SkVarinfo v) when v.Cil.vid = aux_vid ->
              (* Replace index by "start index" variable *)
              let aux_expression =
                VS.fold
                  (fun index expr ->
                     (T.replace_expression
                        ~in_subscripts:true
                        (T.mkVarExpr index)
                        (T.mkVarExpr (T.left_index_vi index)) expr))
                       xinfo.index_set e
              in
                assgn_list@[(T.SkVarinfo v, aux_expression)]
            | _ ->
              assgn_list@[(T.SkVarinfo (VSOps.find_by_id aux_vid aux_vs)), f])
         aux_ef [])
      f
  in
  (new_stv, new_func)

let same_aux old_aux new_aux =
  if IM.cardinal old_aux != IM.cardinal new_aux
  then false
  else
    IM.fold
      (fun n_vid (n_expr, n_f) same ->
         try
           (let  o_expr, o_f = IM.find n_vid old_aux in
            if o_f = n_f then true && same else false)
         with Not_found -> false)
      new_aux
      true

let reduction_with_warning stv expset expr =
  let reduced_expression = reduce_full stv expset expr in
  if (expr = reduced_expression) && !debug then
    begin
      Format.fprintf Format.std_formatter
        "%sWarning%s : expression @;%a@; unchanged after \
         reduction with state %a @; and expressions %a @."
        (PpHelper.color "red") PpHelper.default
        SPretty.pp_skexpr reduced_expression
        VSOps.pvs stv
        (fun fmt a -> SPretty.pp_expr_set fmt a) expset
    end
  else ();
  reduced_expression


(** Discover a set a auxiliary variables for a given variable.
    @param stv the set of state variables.
    @param idx the set of index variables.
    @param input_func the input function.
    @param varid the id of the variable we're analyzing.
    @return a pair of auxiliary variables and auxiliary functions.
*)
let discover_for_id stv (idx, update) input_func varid =
  GenVars.init ();
  init ();
  let init_idx_exprs = create_symbol_map idx in
  let init_exprs = create_symbol_map stv in
  let init_i = { state_set = stv ;
                 state_exprs = init_exprs ;
                 index_set = idx ;
                 index_exprs = init_idx_exprs ;
                 inputs = T.ES.empty
               }
  in
  (** Fixpoint stops when the set of auxiliary varaibles is stable,
      which means the set of auxiliary variables hasn't changed and
      the functions assiocated to these auxilary variables haven't
      changed.
  *)
  let rec fixpoint i xinfo aux_var_set aux_var_map =
    if !debug then Format.printf "Unrolling %i@."i else ();

    let new_xinfo, (new_var_set, new_aux_exprs) =
      (** Find the new expressions by expanding once. *)
      let exprs_map, input_expressions =
        exec_once {xinfo with inputs = T.ES.empty} input_func
      in
      (** Reduce the depth of the state variables in the expression *)
      let new_exprs =
        IM.map
          (reduction_with_warning xinfo.state_set T.ES.empty)
          exprs_map
      in
      (** Compute the new expressions for the index *)
      let xinfo_index = { state_set = xinfo.index_set ;
                          state_exprs = xinfo.index_exprs ;
                          index_set = VS.empty ;
                          index_exprs = IM.empty ;
                          inputs = T.ES.empty;
                        }
      in
      let new_idx_exprs =
        let full_map, _ = exec_once ~silent:true xinfo_index update in
        VS.fold
          (fun vi map -> IM.add vi.Cil.vid (IM.find vi.vid full_map) map)
          xinfo.index_set IM.empty
      in
      (** Find the new set of auxliaries by analyzing the expressions at the
          current expansion level *)

      let aux_var_set, aux_var_map =
        find_auxiliaries
          xinfo
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
    if (i > !max_exec_no) || (same_aux aux_var_map new_aux_exprs)
    then
      new_xinfo, (new_var_set, new_aux_exprs)
    else
      fixpoint (i + 1) new_xinfo new_var_set new_aux_exprs
  in

  let _ , (aux_vs, aux_ef) =
    fixpoint 0 init_i VS.empty IM.empty
  in
  (* Filter out the auxiliaries that are just duplicates of a state variable. *)


  VS.iter (fun vi -> IH.add discovered_aux vi.Cil.vid vi) aux_vs;
  (** Finally add the auxliaries at the beginning of the function. Since the
      auxliaries depend only on the inputs and not the value of the state
      variables we can safely add the assignments (or let bindings) at
      the beginning.
      Return the union of the new auxiliaries and the state variables.
  *)
  if !debug then
    printf "@.DISCOVER for variable %i finished.@." varid;
  printf "@.NEW VARIABLES : %a@." VSOps.pvs aux_vs;


  compose init_i input_func aux_vs aux_ef



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


let discover stv input_func (idx, (i,g,u)) =
  T.create_boundary_variables idx;

  aux_init (VS.union stv idx);
  (** Analyze the index and produce the update function for
      the index.
  *)
  let ranked_stv = rank_by_use (uses stv input_func) in
  List.fold_left
    (fun (new_stv, new_func)  (vid, _) ->
       discover_for_id new_stv (idx, u) new_func vid)
    (stv, input_func)
    ranked_stv
