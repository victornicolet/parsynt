open Format
open Utils
open Core.Std
open SketchTypes
open SPretty
open PpHelper
open Cil2Func
open Racket

open Utils.ListTools

module VS = VS
module SM = Map.Make (String)
module Ct = CilTools

module Body = SketchBody
module Join = SketchJoin

let iterations_limit = ref 10
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

let is_empty_symbDefs =
  function
  | Integers [] | Booleans [] | Reals [] | RoArray (_, []) -> true
  | _ -> false


(** Sketch -> Rosette sketch *)
let main_struct_name = "$"
let join_name = "__join__"
let body_name = "__loop_body__"
let init_state_name = "__$0__"

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
             ~f:(fun str i -> str^" "^array_name^"$"^(string_of_int i))
         in str_list@[cell_names])



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
               ~f:(fun i -> array_name^"$"^(string_of_int i))
           in
           fp fmt "(define-symbolic %a %s)@." pp_string_list cell_names sty;
           fp fmt "(define %s (vector %a))@."
             array_name pp_string_list cell_names)
  end;
  string__symbs_of_symbDef sd


let pp_ne_symbdefs fmt sd =
  if is_empty_symbDefs sd
  then (Format.fprintf fmt "" ; [""])
  else
    begin
      pp_symbDef fmt sd
    end

let strings_of_symbdefs symbdef =
  ignore(pp_ne_symbdefs str_formatter symbdef); flush_str_formatter ()


(** Define the state structure with an equality preidcate *)
let pp_state_definition fmt main_struct =
  pp_struct_defintion fmt main_struct;
  pp_force_newline fmt ();
  pp_struct_equality fmt main_struct

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


(** Loop body *)

let pp_loop_body fmt (loop_body, state_vars, state_struct_name) =
let state_arg_name = "__s" in
  let field_names = VSOps.namelist state_vars in
  Format.fprintf fmt "(lambda (%s i)@.@[<hov 2>(let@;(%a) %a)@])"
    state_arg_name
    (pp_assignments state_struct_name state_arg_name)
    (ListTools.pair field_names field_names)
    pp_sklet loop_body

let pp_loop fmt (loop_body, state_vars) state_struct_name =
  pp_comment fmt "Functional representation of the loop body.";
  Format.fprintf fmt
    "(define (%s s start end)@; \
@[<hov 2>(Loop @[<hov 2>start end %d s@] @.\
@[<hov 2> %a@])@])@."
    body_name
    !iterations_limit
    pp_loop_body (loop_body, state_vars, state_struct_name)



(** Join operator *)
let pp_join_body fmt (join_body, state_vars, lstate_name, rstate_name) =

  let left_state_vars = VSOps.vs_with_suffix state_vars "-$L" in
  let right_state_vars = VSOps.vs_with_suffix state_vars "-$R" in
  let lvar_names = VSOps.namelist left_state_vars in
  let rvar_names = VSOps.namelist right_state_vars in
  let field_names = VSOps.namelist state_vars in
  set_hole_vars left_state_vars right_state_vars;
  Format.fprintf fmt
    "@[<hov 2>(let@.@[<hov 2> (%a@;%a)@]@;@[<hov 2>%a@])@]@."
    (pp_assignments main_struct_name lstate_name)
    (ListTools.pair lvar_names field_names)
    (pp_assignments main_struct_name rstate_name)
    (ListTools.pair rvar_names field_names)
    pp_sklet join_body



let pp_join fmt (join_body, state_vars) =
  let lstate_name = "$L" in
  let rstate_name = "$R" in
  Format.fprintf fmt
    "(define (%s %s %s)@.@[<hov 2>%a@])@."
    join_name  lstate_name rstate_name
    pp_join_body (join_body, state_vars, lstate_name, rstate_name)

(** Some state definitons *)


let pp_states fmt state_vars read_vars st0 reach_consts =
  let s0_sketch_printer =
    pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
      (fun fmt vi ->
        Format.fprintf fmt "(choose 0 1 #t #f)")
  in
  Format.fprintf fmt
    "@[(define %s (%s %a))@]@."
    init_state_name main_struct_name
    s0_sketch_printer (VSOps.varlist state_vars);

  let st0_vars = VSOps.vs_with_suffix state_vars "0" in
  ignore(pp_symbolic_definitions_of fmt
           (VS.filter
              (fun vi -> not (IM.mem vi.Cil.vid reach_consts)) st0_vars));
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
               Format.fprintf fmt "%s" vi.Cil.vname)))
        li)
    (VSOps.bindings st0_vars)


(** The synthesis problem in Rosette *)
let pp_verification_condition fmt (s0, i_st, i_m, i_end) =
  Format.fprintf fmt
    "@[<hov 2>(%s-eq?@. %a @.@[<hov 2>(%s@; %a@; %a)@])@]@."
    main_struct_name
    pp_body_app (body_name, s0, i_st, i_end)
    join_name
    pp_body_app (body_name, s0, i_st, i_m)
    pp_body_app (body_name, init_state_name, i_m, i_end)


let pp_synth_body fmt (s0, state_vars, symbolic_variable_names) =
  Format.fprintf fmt
    "@[<hov 2>#:forall (list %a)@]@." pp_string_list symbolic_variable_names;
  Format.fprintf fmt
    "@[<hov 2>#:guarantee @[(assert @.@[<hov 2>(and@. %a)@])@]@]@."
    (pp_print_list
       (fun fmt (i_st, i_m, i_end) ->
         pp_verification_condition fmt (s0, i_st, i_m, i_end)))
    [(0,0,0);(0,0,9);(0,9,9);(0,4,9);(0,5,9);(3,6,9);(9,9,9)]



let pp_synth fmt s0 state_vars symb_var_names =
  Format.fprintf fmt
    "@[(define odot@.@[<hov 2>(synthesize@.%a)@])@]@."
    pp_synth_body (s0, state_vars, symb_var_names)


let pp_rosette_sketch fmt
    (read, state, all_vars, loop_body, join_body, reach_consts) =
  let state_vars = VSOps.subset_of_list state all_vars in
  let read_vars =
    VS.diff
    (remove_interpreted_symbols
      (VSOps.subset_of_list read all_vars))
      state_vars
  in
  let field_names =
    List.map (VSOps.varlist state_vars) ~f:(fun vi -> vi.Cil.vname) in
  let main_struct = (main_struct_name, field_names) in
  let st0 = "$initial" in
  (** SPretty configuration for the current sketch *)
  SPretty.state_struct_name := main_struct_name;
  let symbolic_variables = pp_symbolic_definitions_of fmt read_vars in
  pp_force_newline fmt ();
  pp_state_definition fmt main_struct;
  pp_force_newline fmt ();
  pp_loop fmt (loop_body, state_vars) main_struct_name;
  pp_join fmt (join_body, state_vars);
  pp_force_newline fmt ();
  pp_comment fmt "Symbolic input state and synthesized id state";
  pp_states fmt state_vars read_vars st0 reach_consts;
  pp_comment fmt "Actual synthesis work happens here";
  pp_force_newline fmt ();
  pp_synth fmt st0 state_vars symbolic_variables
