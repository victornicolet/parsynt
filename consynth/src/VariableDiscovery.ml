open Cil
open Utils
open Pretty
open ExpressionReduction

module Sx = SymbExe
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
      let letin_uses = aux_used_stvs stv inpt IM.empty in
      IM.merge merge_union new_uses letin_uses
    | T.SkLetExpr velist -> List.fold_left used_in_assignment map velist

  and used_in_assignment map (v, expr) =
    let vi = check_option (T.vi_of v) in
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
let find_auxiliaries stv expr other_exprs aux_var_set aux_var_map =
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
         let fe' = Sx.exec_once ~silent:true stv other_exprs fe in
         (IM.find vid fe') = fe)
  in
  let update_aux (aux_vs, aux_exprs) ce =
    (* The expression is exactly the expression of a aux *)
    try
      let expr_func_list = find_ce ce aux_exprs in
      (* TODO : how do we choose which expression to use in this
         case ? Now only pick the first expression to come.
      *)
      let vid, (e, f) = List.nth expr_func_list 0 in
      let new_aux_exprs = IM.add vid (e, T.identity_sk) aux_exprs in
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
            (aux_vs, aux_exprs)
        end
  in
  List.fold_left update_aux (aux_var_set, aux_var_map) (candidates expr)

(** Given a set of auxiliary variables and the associated functions,
    and the set of state variable and a function, return a new set
    of state variables and a function.
*)
let compose stv stv_func aux_vs aux_ef =
  let new_stv = VS.union stv aux_vs in
  let new_func =
    IM.fold
      (fun aux_vid (e, f) assgn_list ->
         assgn_list@[(T.skVarinfo (VSOps.find_by_id aux_vid)),
                    ])
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
  let rec fixpoint cur_exprs cur_idx_exprs aux_var_set aux_var_map =
    let new_exprs =
      Sx.exec_once ~index_set:idx ~index_exprs:cur_idx_exprs
        stv cur_exprs input_func
    in
    let aux_var_set, aux_var_map =
      find_auxiliaries stv (IM.find varid new_exprs) cur_exprs
        aux_var_set aux_var_map
    in
    let new_idx_exprs =
      Sx.exec_once ~silent:true idx cur_idx_exprs update in
    new_exprs, new_idx_exprs, (aux_var_set, aux_var_map)
  in
  let _, _, (aux_vs, aux_ef) =
    fixpoint init_exprs init_idx_exprs VS.empty IM.empty
  in
  (VS.union stv aux_vs),
  compose (** Compose the new aux functions and the old function *)


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
  (** Analyze the index and produce the update function for
      the index.
  *)
  let ranked_stv = rank_by_use (uses stv input_func) in
  List.fold_left
    (fun (new_stv, new_func)  (vid, _) ->
       discover_for_id new_stv (idx, u) new_func vid)
    (stv, input_func)
    ranked_stv
