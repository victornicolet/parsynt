open RAst
open ExtString
open FuncTypes
open Format

module Tbb = Tbb
module Cf = Conf

exception Expr_exn of expr list

(** In the join, remove the "state structure" assignments. *)
let is_struct_assgn (id,e) =
  match e with
  | Apply_e (f, el) ->
    (match f with
     | Id_e struct_mem_id ->
       String.starts_with struct_mem_id
         (Cf.get_conf_string "rosette_struct_name")
     | _ -> false)
    &&
    (match el with
     | [hd] ->
       (match hd with
        | Id_e id ->
          (id = (Cf.get_conf_string "rosette_struct_name")^"R" ||
           id = (Cf.get_conf_string "rosette_struct_name")^"L")
        | _ -> false)
     | _ -> false)
  | _ -> false

let rec rem_struct_assigns (e : RAst.expr) =
  match e with
  | Let_e (assgn_list, e')
  | Letrec_e (assgn_list, e') ->
    let filtered_assgns =
      List.filter (fun a -> not (is_struct_assgn a)) assgn_list
    in
    let re' = rem_struct_assigns e' in
    if filtered_assgns = [] then re' else Let_e (filtered_assgns, re')

  | _ -> e

(* Identify the join function and return its body *)
let identify_join_func e =
  match e with
  | Def_e (id_list, body) ->
    List.length id_list = 5 &&
    (List.nth id_list 0 = Cf.get_conf_string "rosette_join_name") &&
    (List.nth id_list 1 = (Cf.get_conf_string "rosette_struct_name")^"L") &&
    (List.nth id_list 2 = (Cf.get_conf_string "rosette_struct_name")^"R")

  | _ -> false

(** If there is an auxiliary, one part of the solver's task is to discover a
    valid initial value for the auxiliary. We retrieve the list defining the
    state struct and then we will be able to associate each expression to a
    variable, the order in the list being defined using the order in the set of
    state variables.
*)
let get_values_init e =
  match e with
  | Def_e (id_list, body) ->
    if List.length id_list = 3 &&
       (List.hd id_list = Cf.get_conf_string "rosette_initial_state_name")
    then
      (match body with
       | Apply_e (f, args) ->
         Some args
       | _ -> None
      )
    else None

  | _ -> None


type solved_sketch_info =
  { join_body : RAst.expr;
    init_values : RAst.expr list option;}

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
  let maybe_init_v =
    try
      List.fold_left
        (fun accu e ->
           match get_values_init e with
           | Some e -> raise (Expr_exn e)
           | None -> accu)
        None el
    with Expr_exn e -> Some e
  in
  { join_body = rem_struct_assigns join_body; init_values = maybe_init_v }
