open Format
open Utils
open Core.Std
open Conf
open SketchTypes
open SPretty
open PpHelper
open Cil2Func
open Racket
open Cil

open Utils.ListTools

module VS = VS
module SM = Map.Make (String)
module Ct = CilTools

module Body = SketchBody
module Join = SketchJoin

let iterations_limit = ref 10

let auxiliary_vars : Cil.varinfo IH.t = IH.create 10

let debug = ref false

(******************************************************************************)

(**
    Compile the Rosette sketch.
    Rosette is using Racket, which is based on s-expresssions
    so we will be using the Sexplib library to convert types
    directly to s-expressions
*)


(** A symbolic definition defines a list of values of a given type,
    the second string in the type corresponds *)

(** Type for building the definitions list *)
type defsRec =
  { ints : string list ;
    reals : string list ;
    bools : string list ;
    vecs : (string * string) list }

(**
     Type suitable for printing s-expressions that will be used
     as Racket macros.
*)
type symbDef =
  | Integers of string list
  | Reals of string list
  | Booleans of string list
  | RoArray of string * string list


let add_to_reals s defs =
  { defs with reals = s::defs.reals }

let add_to_booleans s defs =
  { defs with bools = s::defs.bools }

let add_to_integers s defs =
  { defs with ints = s::defs.ints }

let add_to_vectors ty s defs =
  let osty = ostring_of_baseSymbolicType ty in
  match osty with
  | Some sty -> { defs with vecs = (s, sty)::defs.vecs }
  | None ->
    eprintf "add_to_vectors : vector of type too complex";
    defs

let adding_function vtype =
  let symb_type = symb_type_of_ciltyp vtype in
  match symb_type with
  | Unit -> identity2
  | Integer -> add_to_integers
  | Real -> add_to_reals
  | Boolean -> add_to_booleans
  | Vector (ty, _) -> add_to_vectors ty
  | _ ->  identity2

let add_varinfo vi defs  =
  (adding_function vi.Cil.vtype) vi.Cil.vname defs

let defsRec_of_varinfos vars_set =
  let empty_defrec = { ints = [] ; reals = []; bools = []; vecs = [] } in
  VS.fold add_varinfo vars_set empty_defrec


(* Convert a record of definitions to a printable set of definitions *)
let defsRec_to_symbDefs defs_rec
  : (symbDef * symbDef * symbDef * (symbDef list) ) =
  let ro_arrays_map =
    List.fold_left
      defs_rec.vecs
      ~init:Utils.SM.empty
      ~f:(fun tmap (vname, sty) ->
          SMTools.update
	    tmap
	    sty
	    [vname]
            (fun pval nval -> pval@nval))
  in
  let ro_arrays = Utils.SM.bindings ro_arrays_map in
  let roArrays = List.map ro_arrays ~f:(fun (k,v) -> RoArray (k, v))
  in
  (
    Integers defs_rec.ints,
    Reals defs_rec.reals,
    Booleans defs_rec.bools,
    roArrays
  )

(** Test if a set of symbolic definitions is empty. It is empty when the list
    of variables to define is empty.
*)
let is_empty_symbDefs =
  function
  | Integers [] | Booleans [] | Reals [] | RoArray (_, []) -> true
  | _ -> false


(** Sketch -> Rosette sketch *)
(** The name of the structure used to represent the state of the loop *)
let main_struct_name = get_conf_string "rosette_struct_name"
(** Name of the join function in the Rosette sketch *)
let join_name = get_conf_string "rosette_join_name"
(** Name of the loop function in the Rosette sketch *)
let body_name = get_conf_string "rosette_loop_body_name"
(** Name of the initial state for the loop in the Rosette sketch *)
let ident_state_name = get_conf_string "rosette_identity_state_name"
let init_state_name = get_conf_string "rosette_initial_state_name"
(** Choose between a very restricted set of values for intials/identity values *)
let base_init_value_choice = get_conf_string "rosette_base_init_value_hole"

(** Return the string of variable names from symbolic definitions. This names
    are the names used when printing the defintions of the symbolic variables
    in pp_symbDef.
    @return A list of strings containing all the names of the variables
    defined using pp_symbDef with the same symbolic definitions. If we an array
    is defined, the names of the cells will be concatenated into one string.
*)
let string__symbs_of_symbDef sd =
  match sd with
  | Integers li ->
    li
  | Reals li ->
    li
  | Booleans li ->
    li
  | RoArray (sty, varnames) ->
    (** Array are finitized and represented
        by vectors containig symbolic values *)
    List.fold_left
      varnames
      ~init:[]
      ~f:(fun str_list array_name ->
          let cell_names =
            List.fold
              (1 -- !iterations_limit)
              ~init:""
              ~f:(fun str i -> str^" "^array_name^main_struct_name^(string_of_int i))
          in str_list@[cell_names])


(** Print the defintions of the variables we need in the sketch. We use
    the basic types of Rosette : integers, reals and booleans. The arrays
    are vectors in Racket, with a finite size defined by the iterations_limit
    parameter in the module.
    The function prints the definitions in the fmt parameter and return a list
    of strings. This list contains the names of the symbolic variables that
    have been defined in the function.

    @param fmt The formatting argument.
    @param sd The symbolic defintions.
    @return A list of strings representing the list of symbols defined.
*)
let pp_symbDef fmt sd =
  let fp = Format.fprintf in
  begin
    match sd with
    | Integers li ->
      fp fmt "(define-symbolic %a integer?)@." pp_string_list li
    | Reals li ->
      fp fmt "(define-symbolic %a real?)@." pp_string_list li
    | Booleans li ->
      fp fmt "(define-symbolic %a boolean?)@." pp_string_list li
    | RoArray (sty, varnames) ->
      (** Array are finitized and represented
          by vectors containig symbolic values *)
      List.iter
        varnames
        ~f:(fun array_name ->
            let cell_names =
              List.map
                (1 -- !iterations_limit)
                ~f:(fun i -> array_name^main_struct_name^(string_of_int i))
            in
            fp fmt "(define-symbolic %a %s)@." pp_string_list cell_names sty;
            fp fmt "(define %s (vector %a))@."
              array_name pp_string_list cell_names)
  end;
  string__symbs_of_symbDef sd

(** Wrapper for pp_symbDef to avoid empty symbolic definitions cases. If there
    is nothing to define, nothing is printed, and the we return a single element
    list containing the empty string.
*)
let pp_ne_symbdefs fmt sd =
  if is_empty_symbDefs sd
  then (Format.fprintf fmt "" ; [""])
  else
    begin
      pp_symbDef fmt sd
    end

let strings_of_symbdefs symbdef =
  ignore(pp_ne_symbdefs str_formatter symbdef); flush_str_formatter ()



(** Handle special constants. For examples, -inf.0 is not supported by Rosette
    so it is replaced by assertions over the input variables with a symbolic
    variables. *)

let handle_special_consts fmt const_exprs_map all_vars =
  let ints, reals, booleans, arrays =
    let i, r, b, ar = defsRec_to_symbDefs (defsRec_of_varinfos all_vars) in
    (string__symbs_of_symbDef i,
     string__symbs_of_symbDef r,
     string__symbs_of_symbDef b,
     List.fold ar ~init:[]
       ~f:(fun li sd -> li@(pp_ne_symbdefs fmt sd)))
  in
  let conj_comp fmt vname inpts op =
    match inpts with
    | [hd] -> Format.fprintf fmt "(%s %s %s)"
                (string_of_symb_binop op) vname hd
    | hd::tl ->
      begin
      Format.fprintf fmt "%a %a %a"
        (fun fmt li ->
           pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "(&& ")
             (fun fmt s -> Format.fprintf fmt "(%s %s %s)@;"
                 (string_of_symb_binop op)
                 vname
                 s) fmt li)
        tl
        (fun fmt s ->
           Format.fprintf fmt
             "(%s %s %s)" (string_of_symb_binop op) vname s)
        hd
        (fun fmt li ->
           pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "")
             (fun fmt s -> Format.fprintf fmt ")")
             fmt li)
        tl
      end

    | [] -> ()

  in
  let ifnotdef s =
    match s with
    | "MAX_INT" -> ()
    | "MIN_INT" -> ()
    | _ -> ()
  in
  let getv s =
    match s with
    | "MAX_INT" -> ()
    | "MIN_INT" -> ()
    | _ -> ()
  in
  IM.fold
    (fun vid econst new_exprs ->
       match econst with
       | SkConst Infnty ->
         ifnotdef "MAX_INT";
         IM.add vid (getv "MAX_INT") new_exprs

       | SkConst NInfnty ->
         ifnotdef "MIN_INT";
         IM.add vid (getv "MIN_INT") new_exprs

       | _ -> IM.add vid () new_exprs
    )
    const_exprs_map IM.empty


(** Pretty print the state structure with an equality predicate. The
    form of the definitions are defined in the Racket module.
*)
let pp_state_definition fmt main_struct =
  pp_struct_defintion fmt main_struct;
  pp_force_newline fmt ();
  pp_struct_equality fmt main_struct

(** Given a set of variables, pretty print their definitions and return
    a list of strings representing the names of the symbolic variables
    that have been defined.
    @param fmt A formatter.
    @param vars The set of variables whose defintion will be printed.
*)
let pp_symbolic_definitions_of fmt vars =
  let (ints, reals, booleans, arrays)
    = defsRec_to_symbDefs (defsRec_of_varinfos vars) in
  let int_symbs, real_symbs, bool_symbs, array_cells =
    pp_ne_symbdefs fmt ints,
    pp_ne_symbdefs fmt reals,
    pp_ne_symbdefs fmt booleans,
    List.fold arrays ~init:[] ~f:(fun li sd -> li@(pp_ne_symbdefs fmt sd))
  in
  int_symbs @ real_symbs @ bool_symbs @ array_cells

(** Pretty print the body of the loop.
    @param loop_body The function representing the loop body.
    @param state_vars The set of state variables of this loop body.
    @param state_struct_name The name of the struct used to represent
    the state of the loop (valuation of the state variables).
*)

let pp_loop_body fmt (loop_body, state_vars, state_struct_name) =
  let state_arg_name = "__s" in
  let field_names = VSOps.namelist state_vars in
  Format.fprintf fmt "@[<hov 2>(lambda (%s i)@;(let@;(%a)@;%a))@]"
    state_arg_name
    (pp_assignments state_struct_name state_arg_name)
    (ListTools.pair field_names field_names)
    pp_sklet loop_body

(** Pretty print the whole loop wrapped in a Racket macro Loop and a function
    deifinition. The name of this function is set in the variable body_name of
    this module.
    @param loop_body The function representing the loop body.
    @param state_vars The set of state variables of this loop body.
    @param state_struct_name The name of the struct used to represent
    the state of the loop (valuation of the state variables).
*)
let pp_loop fmt (loop_body, state_vars) state_struct_name =
  pp_comment fmt "Functional representation of the loop body.";
  Format.fprintf fmt
    "@[<hov 2>(define (%s s %s %s)@;\
     @[<hov 2>(Loop %s %s %d s@;%a)@])@]@.@."
    body_name
    !start_index_name
    !end_index_name
    !start_index_name
    !end_index_name
    !iterations_limit
    pp_loop_body (loop_body, state_vars, state_struct_name)



(** Pretty print the body of the join function in the Rosette sketch.
    @param join_body The function of the join.
    @param state_vars The set of state variables.
    @param lstate_name The name of the left state argument of the join.
    @param rstate_name The name of the right state argument of the join.
*)
let pp_join_body fmt (join_body, state_vars, lstate_name, rstate_name) =

  let left_state_vars = VSOps.vs_with_prefix state_vars
      (Conf.get_conf_string "rosette_join_left_state_prefix") in
  let right_state_vars = VSOps.vs_with_prefix state_vars
      (Conf.get_conf_string "rosette_join_right_state_prefix") in
  let lvar_names = VSOps.namelist left_state_vars in
  let rvar_names = VSOps.namelist right_state_vars in
  let field_names = VSOps.namelist state_vars in
  set_hole_vars left_state_vars right_state_vars;
  Format.fprintf fmt
    "@[<hov 2>(let@;(%a@;%a)@;%a)@]"
    (pp_assignments main_struct_name lstate_name)
    (ListTools.pair lvar_names field_names)
    (pp_assignments main_struct_name rstate_name)
    (ListTools.pair rvar_names field_names)
    pp_sklet join_body


(** Pretty print the join function using the body pretty printing function
    wrapped in a defintion. The name of the function is defined in the
    join_name variable in the module.
    @param join_body The function of the join.
    @param state_vars The set of state variables.
*)
let pp_join fmt (join_body, state_vars) =
  let lstate_name = main_struct_name^"L" in
  let rstate_name = main_struct_name^"R" in
  Format.fprintf fmt
    "@[<hov 2>(define (%s %s %s)@;%a)@]@.@."
    join_name  lstate_name rstate_name
    pp_join_body (join_body, state_vars, lstate_name, rstate_name)

(** Some state definitons *)

(** Pretty print the state (Racket structs) that we need in the Rosette
    sketch.
    @param state_vars The state variable of the loop in the current problem.
    @param read_vars The read-only variable in the current problem.
    @param st0 The name of the inital state.
    @param reach_consts A mapping from variable IDs to expressions. If a binding
    from a variable id to an expression exists, then the value of the variable
    will be set to this expression in the inital state of the loop.
*)
let pp_states fmt state_vars read_vars st0 reach_consts =
  let s0_sketch_printer =
    pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
      (fun fmt vi ->
         Format.fprintf fmt "%s" base_init_value_choice)
  in
  (** Pretty print the identity state, with holes *)
  Format.fprintf fmt
    "@[(define %s (%s %a))@]@."
    ident_state_name main_struct_name
    s0_sketch_printer (VSOps.varlist state_vars);

  let st0_vars = VSOps.vs_with_suffix state_vars "0" in
  ignore(pp_symbolic_definitions_of fmt
           (VS.filter
              (fun vi -> not (IM.mem vi.Cil.vid reach_consts)) st0_vars));
  (** Handle special constants such as Infnty and NInfnty to create the
      necessary assertions and symbolic variables *)
  let mod_consts = handle_special_consts fmt reach_consts in
  (** Pretty print the initial states, with reaching constants and holes
      for the auxiliaries discovered *)
  Format.fprintf fmt
    "@[(define %s (%s %a))@]@."
    st0
    main_struct_name
    (fun fmt li ->
       (ppli fmt ~sep:" "
          (fun fmt (vid, vi) ->
             (if IM.mem vid reach_consts
              then
                pp_skexpr fmt (IM.find vid reach_consts)
              else
                (if IH.mem auxiliary_vars vid
                 then
                   Format.fprintf fmt "%s" base_init_value_choice
                 else
                   Format.fprintf fmt "%s" vi.Cil.vname))))
         li)
    (VSOps.bindings st0_vars)


(** Pretty print one verification condition, the loop
    from a starting index to an end index is split over a index
    i_m between the two.
    @param s0 The name of the inital state.
    @param i_st The starting index for this instance.
    @param i_m The splitting index for this instance.
    @param i_end The end index for this instance.
*)
let pp_verification_condition fmt (s0, i_st, i_m, i_end) =
  Format.fprintf fmt
    "@[<hov 2>(%s-eq?@;%a@;(%s %a %a))@]"
    main_struct_name
    pp_body_app (body_name, s0, i_st, i_end)
    join_name
    pp_body_app (body_name, s0, i_st, i_m)
    pp_body_app (body_name, init_state_name, i_m, i_end)

(** Pretty print the whole body of the synthesis problem. (The set of
    verification conditions is hardcoded here now, we have to change that).
    @param s0 The name of the initial state.
    @param state_vars The set of state variables.
    @param symbolic_variable_names The list of symbolic variable names that will
    have a universal quantifier over.
*)
let pp_synth_body fmt (s0, state_vars, symbolic_variable_names) =
  Format.fprintf fmt
    "@[<hov 2>#:forall (list %a)@]" pp_string_list symbolic_variable_names;
  Format.fprintf fmt
    "@[<hov 2>#:guarantee @[(assert@;(and@;%a))@]@]"
    (pp_print_list
       (fun fmt (i_st, i_m, i_end) ->
          pp_verification_condition fmt (s0, i_st, i_m, i_end)))
    [(0,2,4);
     (0,3,9);
     (0,7,9);
     (0,4,9);
     (0,5,7);
     (3,6,9);
     (2,7,9)]


(** Pretty-print a synthesis problem wrapped in a defintion for further
    access to the solved problem
*)
let pp_synth fmt s0 state_vars symb_var_names =
  Format.fprintf fmt
    "@[<hov 2>(define odot (synthesize@;%a))@.@."
    pp_synth_body (s0, state_vars, symb_var_names)

(** Main interface to print the sketch of the whole problem.
    @param fmt A Format.formatter
    @param read A list of variable ids representing the subset of read-only
    variables.
    @param state A list of variables ids representing the set of state
    variables.
    @param all_vars The set of all the variables in the problem.
    @param loop_body The loop body in a functional form.
    @param join_body The sketch of the join for the loop body.
    @param idx The set of index variables.
    @param i The iniitalization of the index.
    @param g AN expression containinf only index variables representing the
    termination condition of the loop.
    @param u A function updating the index from one iteration to another.
    @param reach_consts A mapping from variable IDs to expressions. If a binding
    from a variable id to an expression exists, then the value of the variable
    will be set to this expression in the inital state of the loop.
*)
let pp_rosette_sketch fmt
    (read, state, all_vars, loop_body, join_body,
     (idx, (i, g, u)), reach_consts) =
  (** State variables *)
  let state_vars = VSOps.subset_of_list state all_vars in
  (** Read variables : force read /\ state = empty *)
  let read_vars =
    VS.diff
      (remove_interpreted_symbols
         (VSOps.subset_of_list read all_vars))
      state_vars
  in
  let field_names =
    List.map (VSOps.varlist state_vars) ~f:(fun vi -> vi.Cil.vname) in
  let main_struct = (main_struct_name, field_names) in
  let st0 = init_state_name in
  (** SPretty configuration for the current sketch *)
  SPretty.state_struct_name := main_struct_name;
  let symbolic_variables = pp_symbolic_definitions_of fmt read_vars in
  pp_force_newline fmt ();
  pp_state_definition fmt main_struct;
  pp_force_newline fmt ();
  pp_loop fmt (loop_body, state_vars) main_struct_name;
  pp_comment fmt "Wrapping for the sketch of the join.";
  pp_join fmt (join_body, state_vars);
  pp_force_newline fmt ();
  pp_comment fmt "Symbolic input state and synthesized id state";
  pp_states fmt state_vars read_vars st0 reach_consts;
  pp_comment fmt "Actual synthesis work happens here";
  pp_force_newline fmt ();
  pp_synth fmt st0 state_vars symbolic_variables
