open Cil
open Utils
open Pretty
open ExpressionReduction
open SymbExe

module T = SketchTypes


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

let aux_var_prefix = ref "aux"

let aux_var_counter = ref 0

let aux_init vs =
  allvars := vs;
  aux_var_counter := 0;
  aux_var_prefix :=
    VS.fold
      (fun vi gen_prefix ->
         if str_contains vi.vname gen_prefix then
           gen_prefix^vi.vname
         else
           gen_prefix)
      !allvars
      !aux_var_prefix

let gen_fresh () =
  let fresh_name = (!aux_var_prefix)^(string_of_int (!aux_var_counter)) in
  incr aux_var_counter;
  let fresh_var = makeVarinfo false fresh_name (TInt (IInt, [])) in
  allvars := VS.add fresh_var !allvars;
  fresh_var


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
  try
    IM.add vi.vid (VS.union vi_used (IM.find vi.vid map)) map
  with Not_found ->
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
let find_auxiliaries xinfo expr aux_var_set aux_var_map =
  let stv = xinfo.state_set in
  let rec is_stv =
    function
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
    | T.SkQuestion (_, e1, e2) -> is_stv e1 || is_stv e2
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
      is_candidate
      handle_candidate
      (fun c -> [])
      (fun v -> [])
      e
  in
  let exists_ce ce =
    IM.exists (fun vid (auxe, f) -> auxe = ce)
  in
  let find_ce ce emap =
    let cemap = IM.filter (fun vid (auxe, f) -> auxe = ce) emap in
    let ce_list = IM.bindings cemap in
    if List.length ce_list < 1 then (raise Not_found) else ce_list
  in
  let find_subexpr ce emap =
    T.rec_expr
      (fun a b -> a@b) []
      (fun e -> exists_ce e emap) (fun e -> find_ce e emap)
      (fun c -> []) (fun v -> [])
      ce
  in
  let match_increment fe =
    List.filter
      (fun (vid,(e, fe)) ->
         let fe' = exec_expr xinfo fe in
         fe' = fe)
  in
  let update_aux (aux_vs, aux_exprs) ce =
    (* The expression is exactly the expression of a aux *)
    try
      let expr_func_list = find_ce ce aux_exprs in
      (* TODO : how do we choose which expression to use in this
         case ? Now only pick the first expression to come.
      *)
      let vid, (e, f) = List.nth expr_func_list 0 in
      let new_aux_exprs = IM.add vid (e, T.SkVar (T.SkState)) aux_exprs in
      (aux_vs, new_aux_exprs)
      with Not_found ->
        let ef_list = find_subexpr ce aux_exprs in
        begin
          if List.length ef_list > 0
          then
            (* A subexpression of the expression is an auxiliary variable *)
            (* TODO : better tactic to choose expressions *)
            let vid, (e, f) = List.nth (match_increment ce ef_list) 0 in
            let new_aux_exprs = IM.add vid (ce, f) aux_exprs in
            (aux_vs, new_aux_exprs)
          else
            (* We have to create a new variable *)
            let new_aux = gen_fresh () in
            let new_aux_vs = VS.add new_aux aux_vs in
            let new_exprs =
              IM.add new_aux.vid (ce, T.SkVar T.SkState) aux_exprs
            in
            (new_aux_vs, new_exprs)
        end
  in
  List.fold_left update_aux (aux_var_set, aux_var_map) (candidates expr)

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
            assgn_list@[(T.SkVarinfo (VSOps.find_by_id aux_vid aux_vs)), f])
         aux_ef [])
      f
  in
  (new_stv, new_func)

(** Discover a set a auxiliary variables for a given variable.
    @param stv the set of state variables.
    @param idx the set of index variables.
    @param input_func the input function.
    @param varid the id of the variable we're analyzing.
    @return a pair of auxiliary variables and auxiliary functions.
*)
let discover_for_id stv (idx, update) input_func varid =
  SymbExe.init ();
  let init_idx_exprs = create_symbol_map idx in
  let init_exprs = create_symbol_map stv in
  let rec fixpoint xinfo aux_var_set aux_var_map =
    let new_exprs =
      exec_once xinfo input_func
    in
    let xinfo_index = { state_set = xinfo.index_set ;
                        state_exprs = xinfo.index_exprs ;
                        index_set = VS.empty ;
                        index_exprs = IM.empty ;
                      }
    in
    let new_idx_exprs =
      exec_once ~silent:true xinfo_index update in
    let aux_var_set, aux_var_map =
      find_auxiliaries xinfo (IM.find varid new_exprs) aux_var_set aux_var_map
    in
    {xinfo with state_exprs = new_exprs;
                index_exprs = new_idx_exprs},
    (aux_var_set, aux_var_map)
  in
  let init_i = { state_set = stv ;
               state_exprs = init_exprs ;
               index_set = idx ;
               index_exprs = init_idx_exprs ;
               }
  in
  let _ , (aux_vs, aux_ef) =
    fixpoint init_i VS.empty IM.empty
  in
  compose init_i input_func aux_vs aux_ef


(** Main algorithm. Discovers new variables that can be useful in parallelizing
    the computation.
    @param stv the set of state variables.
    @param input_func the input function of the algorithm.
    @param igu the init, guard and update statements of the enclosing loop. It
    will be used in computing the symbolic index in the algorithm.
    @return A new set of state variables and a new function with the varaibles
    discovered by the algortihm.
*)
let discover stv input_func (idx, (i,g,u)) =
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
