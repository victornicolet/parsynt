open RAst
open ExtString
open FuncTypes
open Format
open Utils

module Tbb = Tbb
module Cf = Conf
module L = List
module Lt = ListTools

exception Expr_exn of expr list

let lstate_name = Conf.get_conf_string "rosette_join_left_state_name"
let rstate_name = Conf.get_conf_string "rosette_join_right_state_name"


(** In the join, remove the "state structure" assignments. *)
let is_struct_assgn (id,e) =
  let rsn = Cf.get_conf_string "rosette_struct_name" in
  match e with
  | Apply_e (f, el) ->
    (match f with
     | Id_e struct_mem_id ->
       String.starts_with struct_mem_id rsn
     | _ -> false)
    &&
    (match el with
     | [hd] ->
       (match hd with
        | Id_e id ->
          (str_begins_with lstate_name id) ||
          (str_begins_with rstate_name id)
        | _ -> false)
     | _ -> false)
  | _ -> false

let rec rem_struct_assigns (e : RAst.expr) =
  match e with
  | Let_e (assgn_list, e')
  | Letrec_e (assgn_list, e') ->
    let filtered_assgns =
      L.filter (fun a -> not (is_struct_assgn a)) assgn_list
    in
    let re' = rem_struct_assigns e' in
    if filtered_assgns = [] then re' else Let_e (filtered_assgns, re')

  | _ -> e

(* Identify the join function and return its body *)
let identify_join_func e =
  let join_name = Cf.get_conf_string "rosette_join_name" in
  match e with
  | Def_e (id_list, body) ->
    (L.length id_list = 5) &&
    (id_list >> 0 = join_name ) &&
    (str_begins_with lstate_name (id_list >> 1)) &&
    (str_begins_with rstate_name (id_list >> 2))

  | _ -> false




(** If there is an auxiliary, one part of the solver's task is to discover a
    valid initial value for the auxiliary. We retrieve the list defining the
    state struct and then we will be able to associate each expression to a
    variable, the order in the list being defined using the order in the set of
    state variables.
*)
let get_values_state state_name e =
  match e with
  | Def_e (id_list, body) ->
    if (List.hd id_list = state_name)
    then
      (match body with
       | Apply_e (f, args) ->
         Some args
       | _ -> None
      )
    else None

  | _ -> None


let get_values_init e =
  get_values_state (Cf.get_conf_string "rosette_initial_state_name") e

let get_values_identity e =
  get_values_state (Cf.get_conf_string "rosette_identity_state_name") e

type solved_sketch_info =
  { join_body : RAst.expr;
    init_values : RAst.expr list option;
    identity_values : RAst.expr list option}

let get_solved_sketch_info (el : RAst.expr list) =
  let join_body =
    try
      (match List.find identify_join_func el with
      | Def_e (_, jbody) -> jbody
      | _ -> raise Not_found)
    with Not_found ->
      (eprintf "Couldn't find a join in the solution... \
                Did we really find a solution ?@.";
       eprintf "Received: %a@." RAst.pp_expr_list el;
       raise Not_found)
  in
  let init_state =
    Lt.some_hd (L.map check_option (L.filter is_some (L.map get_values_init el)))
  in
  let identity_state =
    Lt.some_hd (L.map check_option (L.filter is_some (L.map get_values_identity el)))
  in
  { join_body = rem_struct_assigns join_body;
    init_values = init_state;
    identity_values = identity_state}
