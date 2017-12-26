open Utils
open Conf
open SketchTypes
open SPretty
open Utils.PpTools
open Cil2Func
open Racket
open Cil

open Utils.ListTools

module SM = Map.Make (String)
module Ct = CilTools
module F = Format

module Body = SketchBody
module Join = SketchJoin

let iterations_limit =
  ref (int_of_string (Conf.get_conf_string "loop_finite_limit"))

let auxiliary_vars : Cil.varinfo IH.t = IH.create 10

let debug = ref (bool_of_string (Conf.get_conf_string "debug_sketch"))


(* Current bitwidth setting *)
let pp_current_bitwidth fmt func_expr =
  F.fprintf fmt "@.(current-bitwidth %s)@.@."
    (if analyze_optype_l func_expr = NonLinear then "6" else "#f")

(******************************************************************************)

(**
    Compile the Rosette sketch.
    Rosette is using Racket, which is based on s-expresssions
    so we will be using the Sexplib library to convert types
    directly to s-expressions
*)


(** A symbolic definition defines a list of values of a given type,
    the second string in the type corresponds *)

type define_symbolic =
  | DefInteger of varinfo list
  | DefReal of varinfo list
  | DefBoolean of varinfo list
  | DefArray of varinfo list
  | DefEmpty

let gen_cell_vars vi =
  ListTools.init !iterations_limit
    (fun i -> {vi with vname = vi.vname^"$"^(string_of_int i)})

let rec pp_define_symbolic fmt def =
  let to_v l  = (List.map (fun vi -> vi.vname) l) in
  match def with
  | DefInteger vil -> F.fprintf fmt "@[(define-symbolic %a integer?)@]@\n"
                        pp_string_list (to_v vil)
  | DefReal vil -> F.fprintf fmt "@[(define-symbolic %a real?)@]@\n"
                     pp_string_list (to_v vil)

  | DefBoolean vil -> F.fprintf fmt "@[(define-symbolic %a boolean?)@]@\n"
                        pp_string_list (to_v vil)
  | DefArray vil ->
    List.iter
      (fun vi ->
          let vars = gen_cell_vars vi in
          pp_define_symbolic fmt
            (match array_type (type_of_ciltyp vi.vtype) with
             | Integer -> DefInteger vars
             | Real -> DefReal vars
             | Boolean -> DefBoolean vars
             | _ -> DefEmpty);
          F.fprintf fmt "@[<hv 2>(define %s@;(vector %a))@]@\n"
            vi.vname pp_string_list (to_v vars)) vil

  | DefEmpty -> ()


let pp_vs_to_symbs fmt except vs =
  (* Populate the types *)
  VS.iter
    (fun vi ->
       if List.mem vi except then ()
       else
         pp_define_symbolic fmt
           (match type_of_ciltyp vi.vtype with
            | Integer -> DefInteger [vi]
            | Boolean -> DefBoolean [vi]
            | Real -> DefReal [vi]
            | Vector (v, _) -> DefArray [vi]
            | _ ->
              (F.eprintf "Unsupported type for variable %s.\
                          This might lead to errors in the sketch."
                 vi.vname;
               DefEmpty))) vs


let input_symbols_of_vs vs =
  VS.fold
    (fun vi symbs ->
       if CilTools.is_like_array vi then
         symbs@(gen_cell_vars vi)
       else
         vi::symbs) vs []

let pp_defined_input fmt vs =
  F.pp_print_list
    ~pp_sep:(fun fmt () -> F.fprintf fmt "@;")
    (fun fmt vi -> F.fprintf fmt "%s" vi.vname)
    fmt (input_symbols_of_vs vs)

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
let base_init_value_choice reaching_consts vi =
  (try
     let e = IM.find vi.vid reaching_consts in
     F.fprintf F.str_formatter "(choose %s %a)"
       (get_conf_string "rosette_base_init_values")
       pp_skexpr e
   with Not_found ->
     F.fprintf F.str_formatter "(choose %s)"
       (get_conf_string "rosette_base_init_values"));
  F.flush_str_formatter ()


(** Handle special constants. For examples, -inf.0 is not supported by Rosette
    so it is replaced by assertions over the input variables with a symbolic
    variables. *)
type special_const =
  | NINFNTY
  | INFNTY

let create fmt input_vars varname =
  pp_comment fmt "Adding special variable with assertions.";
  let pp_loc_assert = F.fprintf fmt "@[<hov 2>(assert (and %a))@]@\n" in
  match varname with
  | INFNTY ->
    let vi = makeVarinfo false "__MAX_INT_" (TInt (IInt, [])) in
    pp_define_symbolic fmt (DefInteger [vi]);
    let input_symbols = input_symbols_of_vs input_vars in
    pp_loc_assert
      (F.pp_print_list
         ~pp_sep:(fun fmt () -> F.fprintf fmt "@;")
         (fun fmt inp_vi -> F.fprintf fmt "(< %s %s)" inp_vi.vname vi.vname))
      input_symbols;
    vi

  | NINFNTY ->
    let vi = makeVarinfo false "__MIN_INT_" (TInt (IInt, [])) in
    pp_define_symbolic fmt (DefInteger [vi]);
    let input_symbols = input_symbols_of_vs input_vars in
    pp_loc_assert
      (F.pp_print_list
         ~pp_sep:(fun fmt () -> F.fprintf fmt "@;")
         (fun fmt inp_vi -> F.fprintf fmt "(> %s %s)" inp_vi.vname vi.vname))
      input_symbols;
    vi

let special_const_table : Cil.varinfo IH.t = IH.create 10

let get_or_create fmt input_vars special_const_typ =
  let special_const_index =
    match special_const_typ with
    | NINFNTY -> 0
    | INFNTY -> 1
  in
  try
    IH.find special_const_table special_const_index
  with Not_found ->
    let vi = create fmt input_vars special_const_typ in
    F.fprintf fmt "@.";
    IH.add special_const_table
      special_const_index vi; vi

let clear_special_consts () = IH.clear special_const_table

let handle_special_consts fmt input_vars reach_consts =
  IM.map
    (fun expr ->
       match expr with
       | SkConst NInfnty ->
         (** Assume all numeric inputs are greater than a symbolic variable.*)
         let vi = get_or_create fmt input_vars NINFNTY in
         SkVar (SkVarinfo vi)

       | SkConst Infnty ->
         let vi = get_or_create fmt input_vars INFNTY in
         SkVar (SkVarinfo vi)

       | _ -> expr) reach_consts



(** Pretty print the state structure with an equality predicate. The
    form of the definitions are defined in the Racket module.
*)
let pp_state_definition fmt main_struct =
  pp_struct_defintion fmt main_struct;
  pp_newline fmt ();
  pp_struct_equality fmt main_struct

(** Given a set of variables, pretty print their definitions and return
    a list of strings representing the names of the symbolic variables
    that have been defined.
    @param fmt A formatter.
    @param vars The set of variables whose defintion will be printed.
*)
let pp_symbolic_definitions_of fmt except_vars vars =
  pp_vs_to_symbs fmt except_vars vars

(** Pretty print the body of the loop.
    @param loop_body The function representing the loop body.
    @param state_vars The set of state variables of this loop body.
    @param state_struct_name The name of the struct used to represent
    the state of the loop (valuation of the state variables).
*)

let pp_loop_body fmt (loop_body, state_vars, state_struct_name) =
  let state_arg_name = "__s" in
  let field_names = VS.namelist state_vars in
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
let pp_loop fmt index_set bnames (loop_body, state_vars) state_struct_name =
  let index_list = VS.varlist index_set in
  let pp_index_low_up =
        (F.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
       (fun fmt vi ->
          let start_vi, end_vi = (IH.find index_to_boundary vi.vid) in
          Format.fprintf fmt "%s %s" start_vi.vname end_vi.vname))
  in
  pp_comment fmt "Functional representation of the loop body.";
  Format.fprintf fmt
    "@[<hov 2>(define (%s %s %a %a)@;\
     @[<hov 2>(Loop %a %d %s@;%a)@])@]@.@."
    body_name                   (* Name of the function *)
    (Conf.get_conf_string "rosette_state_param_name") (* Name of the input state *)
    pp_index_low_up index_list (* List of local lower and upper bounds - args *)
    pp_string_list bnames
    pp_index_low_up index_list (* List of local lower and upper bounds - loop *)
    (int_of_string (Conf.get_conf_string "rosette_loop_iteration_limit"))
    (Conf.get_conf_string "rosette_state_param_name")

    pp_loop_body (loop_body, state_vars, state_struct_name)



(** Pretty print the body of the join function in the Rosette sketch.
    @param join_body The function of the join.
    @param state_vars The set of state variables.
    @param lstate_name The name of the left state argument of the join.
    @param rstate_name The name of the right state argument of the join.
*)
let pp_join_body fmt (join_body, state_vars, lstate_name, rstate_name) =

  let left_state_vars = VS.vs_with_prefix state_vars
      (Conf.get_conf_string "rosette_join_left_state_prefix") in
  let right_state_vars = VS.vs_with_prefix state_vars
      (Conf.get_conf_string "rosette_join_right_state_prefix") in
  let lvar_names = VS.namelist left_state_vars in
  let rvar_names = VS.namelist right_state_vars in
  let field_names = VS.namelist state_vars in
  printing_sketch := true;
  Format.fprintf fmt
    "@[<hov 2>(let@;(%a@;%a)@;%a)@]"
    (pp_assignments main_struct_name lstate_name)
    (ListTools.pair lvar_names field_names)
    (pp_assignments main_struct_name rstate_name)
    (ListTools.pair rvar_names field_names)
    pp_sklet join_body;
  printing_sketch := false


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
  let reach_consts = handle_special_consts fmt read_vars reach_consts in
  let s0_sketch_printer =
    F.pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
      (fun fmt vi ->
         Format.fprintf fmt "%s" (base_init_value_choice reach_consts vi))
  in
  (** Pretty print the identity state, with holes *)
  Format.fprintf fmt
    "@[(define %s (%s %a))@]@."
    ident_state_name main_struct_name
    s0_sketch_printer (VS.varlist state_vars);

  (** Handle special constants such as Infnty and NInfnty to create the
      necessary assertions and symbolic variables *)

  (** Pretty print the initial states, with reaching constants and holes
      for the auxiliaries discovered *)
  Format.fprintf fmt
    "@[(define (%s %s %s) (%s %a))@]@."
    st0
    "_begin_" "end"
    main_struct_name
    (fun fmt li ->
       (ppli fmt ~sep:" "
          (fun fmt (vid, vi) ->
             (if IM.mem vid reach_consts
              then
                pp_skexpr fmt
                  (try
                     replace_all_subs
                       ~tr:[SkConst (CInt 0); SkConst (CInt64 0L)]
                       ~by:[SkVar (SkVarinfo {vi with vname = "_begin_"});
                            SkVar (SkVarinfo {vi with vname = "_begin_"})]
                       ~ine:(IM.find vid reach_consts)
                  with _ -> IM.find vid reach_consts)
              else
                (if IH.mem auxiliary_vars vid
                 then
                   Format.fprintf fmt "%s"
                     (base_init_value_choice reach_consts vi)
                 else
                   begin
                     F.eprintf
                       "@.%sERROR : \
                        Variable %s should be initialized or auxiliary.%s@."
                       (color "red") vi.Cil.vname color_default;
                     failwith "Unexpected variable."
                   end))))
         li)
    (VS.bindings state_vars)


(** Pretty print one verification condition, the loop
    from a starting index to an end index is split over a index
    i_m between the two.
    @param s0 The name of the inital state.
    @param i_st The starting index for this instance.
    @param i_m The splitting index for this instance.
    @param i_end The end index for this instance.
*)
let pp_verification_condition fmt (s0, bnm, i_st, i_m, i_end) min_dep_len =
  let bnds = (bnm, i_st, i_m, i_end) in
  if i_m - i_st >= min_dep_len && i_end - i_m >= min_dep_len then
    Format.fprintf fmt
      "@[<hov 2>(%s-eq?@;%a@;(%s %a %a))@]"
      main_struct_name
      pp_body_app (body_name, s0, bnds, i_st, i_end)
      join_name
      pp_body_app (body_name, s0, bnds, i_st, i_m)
      pp_body_app (body_name, init_state_name, bnds, i_m, i_end)
  else
    ()

(** Pretty print the whole body of the synthesis problem. (The set of
    verification conditions is hardcoded here now, we have to change that).
    @param s0 The name of the initial state.
    @param state_vars The set of state variables.
    @param symbolic_variable_names The list of symbolic variable names that will
    have a universal quantifier over.
*)
let pp_synth_body fmt (s0, bnm, state_vars, defined_input_vars, min_dep_len) =
  Format.fprintf fmt
    "@[<hov 2>#:forall @[<hov 2>(list %a)@]@]@\n"
    pp_defined_input defined_input_vars;
  Format.fprintf fmt
    "@[<hov 2>#:guarantee @[(assert@;(and@;%a))@]@]"
    (F.pp_print_list
       (fun fmt (i_st, i_m, i_end) ->
          pp_verification_condition fmt (s0, bnm, i_st, i_m, i_end)
            min_dep_len))
    Conf.verification_parameters


(** Pretty-print a synthesis problem wrapped in a defintion for further
    access to the solved problem
*)
let pp_synth fmt s0 bnames state_vars read_vars min_dep_len =
  Format.fprintf fmt
    "@[<hov 2>(define odot (synthesize@;%a))@.@."
    pp_synth_body (s0, bnames, state_vars, read_vars, min_dep_len)

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
let pp_rosette_sketch fmt (sketch : sketch_rep) =
  clear_special_consts ();
  let min_dep_len = sketch.min_input_size in
  (** State variables *)
  let state_vars = sketch.scontext.state_vars in
  (** Read variables : force read /\ state = empty *)
  let read_vars =
    VS.diff
      (remove_interpreted_symbols sketch.scontext.used_vars)
      (VS.union state_vars sketch.scontext.index_vars)
  in
  let idx = sketch.scontext.index_vars in
  let field_names =
    List.map (fun vi -> vi.Cil.vname) (VS.varlist state_vars) in
  let main_struct = (main_struct_name, field_names) in
  let st0 = init_state_name in
  (* Global bound name "n" *)
  let bnd_vars =
    List.fold_left
      (fun name_list expr ->
         match expr with
         | Some (SkVar (SkVarinfo vi)) -> name_list@[vi]
         | _ -> name_list)
      []
      (if sketch.uses_global_bound then
          [(SketchTypes.get_loop_bound sketch)]
       else [])
  in
  let bnames =
    List.map (fun vi -> vi.vname) bnd_vars
  in
  (** SPretty configuration for the current sketch *)
  SPretty.state_struct_name := main_struct_name;
  pp_current_bitwidth fmt sketch.loop_body;
  pp_symbolic_definitions_of fmt bnd_vars read_vars;
  pp_newline fmt ();
  pp_state_definition fmt main_struct;
  pp_newline fmt ();
  pp_loop fmt idx bnames (sketch.loop_body, state_vars) main_struct_name;
  pp_comment fmt "Wrapping for the sketch of the join.";
  pp_join fmt (sketch.join_body, state_vars);
  pp_newline fmt ();
  pp_comment fmt "Symbolic input state and synthesized id state";
  pp_states fmt state_vars read_vars st0 sketch.reaching_consts;
  pp_comment fmt "Actual synthesis work happens here";
  pp_newline fmt ();
  pp_synth fmt st0 bnames state_vars read_vars min_dep_len
