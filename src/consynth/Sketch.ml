(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

    Parsynt is free software: you can redistribute it and/or modify
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

(*
   1 - Printing sketches for Rosette (Scheme lang)
   2 - Printing sketches for other sygus solvers (Synthlib v2) (Work in progress...)
*)

open Beta
open Utils
open Conf
open Fn
open FnPretty
open Format
open Utils.PpTools
open Cil2Func
open Racket
open Random
open Synthlib
open Synthlib2ast

open Utils.ListTools

module SM = Map.Make (String)
module Ct = CilTools
module F = Format

module Join = SketchJoin



let auxiliary_vars : fnV IH.t = IH.create 10

let debug = ref (bool_of_string (Conf.get_conf_string "debug_sketch"))

let concrete_sketch = ref false



(******************************************************************************)

(** 1 - ROSETTE
    Compile the Rosette sketch.
    Rosette is using Racket, which is based on s-expresssions
    so we will be using the Sexplib library to convert types
    directly to s-expressions
*)


(* Current bitwidth setting *)
let pp_current_bitwidth fmt func_expr =
  F.fprintf fmt "@.(current-bitwidth %s)@.@."
    (if analyze_optype func_expr = NonLinear then "6" else "#f")


(** A symbolic definition defines a list of values of a given type,
    the second string in the type corresponds *)

type define_symbolic =
  | DefInteger of fnV list
  | DefReal of fnV list
  | DefBoolean of fnV list
  | DefArray of (fnV * int) list
  | DefMatrix of (fnV * int * int) list
  | DefMatrix3D of (fnV * int * int * int) list
  | DefRecord of (fnV * string * ((string * fn_type) list) * (int * int)) list
  | DefEmpty


let gen_array_cell_vars ~num_cells:n vi =
  let gen_cell i =
    {vi with vname = vi.vname^"$"^(string_of_int i)}
  in
  ListTools.init (n - 1) gen_cell


let gen_mat_cell_vars ~num_lines:n ~num_cols:m vi =
  ListTools.init (n - 1)
    (fun i ->
       (ListTools.init (m - 1)
          (fun j -> {vi with vname = vi.vname^"$"^(string_of_int i)^"$"^(string_of_int j)})))

let gen_mat3d_cell_vars ~num_lines:n ~num_cols:m ~num_bicols:o vi =
  ListTools.init (n - 1)
    (fun i ->
       (ListTools.init (m - 1)
        (fun j ->
           (ListTools.init (o - 1)
              (fun k -> {vi with vname = vi.vname^"$"^(string_of_int i)^"$"^(string_of_int j)^"$"^(string_of_int k)})))))


let rec pp_define_symbolic fmt def =
  let to_v l  = (List.map (fun vi -> vi.vname) l) in
  match def with
  | DefInteger vil ->
    if !concrete_sketch then
        F.fprintf fmt "@[(define-values (%a) (values %a))@]@\n"
          pp_string_list (to_v vil)
          (pp_break_sep_list (fun fmt i -> F.fprintf fmt "%i" i))
          (ListTools.init ((List.length vil) - 1) (fun i -> Random.int 10))
    else
        F.fprintf fmt "@[(define-symbolic %a integer?)@]@\n"
          pp_string_list (to_v vil)

  | DefReal vil ->
    if !concrete_sketch then
      F.fprintf fmt "@[(define-values (%a) (values %a))@]@\n"
        pp_string_list (to_v vil)
        (pp_break_sep_list (fun fmt i -> F.fprintf fmt "%2.3f" i))
        (ListTools.init ((List.length vil) - 1) (fun i -> Random.float 10.0))
    else
      F.fprintf fmt "@[(define-symbolic %a real?)@]@\n"
        pp_string_list (to_v vil)

  | DefBoolean vil ->
    if !concrete_sketch then
      F.fprintf fmt "@[(define-values (%a) (values %a))@]@\n"
        pp_string_list (to_v vil)
        (pp_break_sep_list (fun fmt i -> F.fprintf fmt "%b" i))
        (ListTools.init ((List.length vil) - 1) (fun i -> Random.bool ()))
    else
      F.fprintf fmt "@[(define-symbolic %a boolean?)@]@\n"
        pp_string_list (to_v vil)

  | DefArray vil ->
    List.iter
      (fun (vi, n) ->
         let vars = gen_array_cell_vars ~num_cells:n vi in
         pp_define_symbolic fmt
           (try
              (match array_type vi.vtype with
               | Integer -> DefInteger vars
               | Real -> DefReal vars
               | Boolean -> DefBoolean vars
               | Record (s, r) -> DefRecord (List.map (fun vi -> vi, s, r, (n, Dimensions.width ())) vars)
               | _ -> DefEmpty)
            with BadType s ->
              failhere __FILE__ "pp_define_symbolic" s);
         F.fprintf fmt "@[<hv 2>(define %s@;(list %a))@]@\n"
           vi.vname pp_string_list (to_v vars)) vil

  | DefMatrix vil ->
    List.iter
      (fun (vi, n, m) ->
         let mvars = gen_mat_cell_vars ~num_lines:n ~num_cols:m vi in
         let avars = gen_array_cell_vars ~num_cells:n vi in
         List.iteri
           (fun i vars ->
              pp_define_symbolic fmt
                (match matrix_type vi.vtype with
                 | Integer -> DefInteger vars
                 | Real -> DefReal vars
                 | Boolean -> DefBoolean vars
                 | _ -> DefEmpty);
              F.fprintf fmt "@[<hv 2>(define %s$%i@;(list %a))@]@\n"
                vi.vname i pp_string_list (to_v vars))
           mvars;
         F.fprintf fmt "@[<hv 2>(define %s@;(list %a))@]@\n"
           vi.vname pp_string_list (to_v avars))
      vil

  | DefMatrix3D vil ->
    List.iter
      (fun (vi, n, m, o) ->
         let nvars = gen_mat3d_cell_vars ~num_lines:n ~num_cols:m ~num_bicols: o vi in
         let mvars = gen_mat_cell_vars ~num_lines:n ~num_cols:m vi in
         let avars = gen_array_cell_vars ~num_cells:n vi in
         (* First iter *)
         List.iteri
           (fun i vars1 ->
                   (* Second iter *)
                   (List.iteri
                       (fun j vars2 ->
                      pp_define_symbolic fmt
                        (match matrix_type vi.vtype with
                         | Integer -> DefInteger vars2
                         | Real -> DefReal vars2
                         | Boolean -> DefBoolean vars2
                         | _ -> DefEmpty);
                      F.fprintf fmt "@[<hv 2>(define %s$%i$%i@;(list %a))@]@\n"
                        vi.vname i j pp_string_list (to_v vars2))
                       vars1))
           nvars;
         List.iteri
           (fun i vars ->
              F.fprintf fmt "@[<hv 2>(define %s$%i@;(list %a))@]@\n"
                vi.vname i pp_string_list (to_v vars))
           mvars;
         F.fprintf fmt "@[<hv 2>(define %s@;(list %a))@]@\n"
           vi.vname pp_string_list (to_v avars))
      vil

  | DefRecord virtl ->
    List.iter
      (fun (vi, name, mems, (n, m)) ->
         let vars =
           List.map
             (fun (name, typ) ->
                let newv = [{vi with vname = vi.vname^"-"^name; vtype = typ}] in
                pp_define_symbolic fmt
                  (match typ with
                   | Integer -> DefInteger newv
                   | Boolean -> DefBoolean newv
                   | Real -> DefReal newv
                   | Vector (v, _) -> DefArray [(newv >> 0, m)]
                   | _ -> DefEmpty);
                newv >> 0, name, typ
             )
             mems
         in
         let vars, _, _ = ListTools.untriple vars in
         F.fprintf fmt "@[<hv 2>(define %s@;(%s %a)@;)@]@\n"
           vi.vname name  pp_string_list (to_v vars)
      )
      virtl

  | DefEmpty -> ()


let pp_vs_to_symbs ?(inner=false) fmt except vs =
  (* Populate the types *)
  VarSet.iter
    (fun vi ->
       if List.mem vi except then ()
       else
         pp_define_symbolic fmt
           (match vi.vtype with
            | Integer -> DefInteger [vi]
            | Boolean -> DefBoolean [vi]
            | Real -> DefReal [vi]
            | Vector (v, _) ->
              (* Support up to 3-dimensional arrays. *)
              (match v with
               | Vector (v2, _) ->
                  (match v2 with
                   | Vector (v3, _) -> DefMatrix3D [(vi, Dimensions.height (), Dimensions.width (),Dimensions.width ())]
                   | _ -> DefMatrix [(vi,Dimensions.height (),Dimensions.width () )])
               | _ -> DefArray [(vi, if inner then Dimensions.width () else Dimensions.height ())])
            | Record (s, rt) ->
              DefRecord [(vi, s, rt, Dimensions.dims () )]
            | _ ->
              (F.eprintf "Unsupported type for variable %s.\
                          This will lead to errors in the sketch."
                 vi.vname;
               DefEmpty))) vs


let rec input_symbols_of_vs vs =
  VarSet.fold
    (fun vi symbs ->
       match vi.vtype with
       | Vector(Vector (Vector _, _),_) ->
         symbs@(List.flatten (List.flatten (gen_mat3d_cell_vars
                                ~num_lines:(Dimensions.height ())
                                ~num_cols:(Dimensions.width ())
                                ~num_bicols:(Dimensions.width ()) vi)))
       | Vector(Vector _, _) ->
         symbs@(List.flatten (gen_mat_cell_vars
                                ~num_lines:(Dimensions.height ())
                                ~num_cols:(Dimensions.width ()) vi))
       | Vector(Record (name, r), _) ->
         symbs@(gen_record_array_cells ~num_records:(Dimensions.height ()) r vi)
       | Vector(t, _) ->
         symbs@(gen_array_cell_vars ~num_cells:(Dimensions.width ()) vi)
       | _ ->
         vi::symbs)
    vs []

and gen_record_array_cells ~num_records:n r vi =
  let ith_cell i =
    List.fold_left
      (fun l (n,t) ->
         let ith_vi_field =
           {vi with vname = vi.vname^"$"^(string_of_int i)^"-"^n}
         in
         match t with
         | Vector(t', _) -> l@(gen_array_cell_vars ~num_cells:(Dimensions.width ()) ith_vi_field)
         | _ -> ith_vi_field::l) [] r
  in
  List.flatten (ListTools.init (n - 1) ith_cell)



let pp_defined_input fmt vs =
  F.pp_print_list
    ~pp_sep:(fun fmt () -> F.fprintf fmt "@;")
    (fun fmt vi -> F.fprintf fmt "%s" vi.vname)
    fmt (input_symbols_of_vs vs)


(* ---------------------------------------------------------------------------- *)
(** Sketch -> Rosette sketch *)
(** The name of the structure used to represent the state of the loop *)
let struct_prefix = get_conf_string "rosette_struct_name"
(** Name of the join function in the Rosette sketch *)
let join_name = get_conf_string "rosette_join_name"
(** Name of the loop function in the Rosette sketch *)
let body_name = get_conf_string "rosette_loop_body_name"
(** Name of the initial state for the loop in the Rosette sketch *)
let ident_state_name = get_conf_string "rosette_identity_state_name"
let init_state_name = get_conf_string "rosette_initial_state_name"
let index_begin = get_conf_string "rosette_index_suffix_start"
let index_end = get_conf_string "rosette_index_suffix_end"
let right_state_prefix = get_conf_string "rosette_join_right_state_prefix"
let left_state_prefix = get_conf_string "rosette_join_left_state_prefix"

(** Choose between a very restricted set of values for intials/identity values *)
let base_init_value_choice fmt (reaching_consts, vi) =
  let base_value fmt () =
    (try
       let e = IM.find vi.vid reaching_consts in
       F.fprintf fmt "(choose %s %a)"
         (get_conf_string "rosette_base_init_values")
         pp_fnexpr e
     with Not_found ->
       F.fprintf fmt "(choose %s)"
         (get_conf_string "rosette_base_init_values"))
  in
  match vi.vtype with
  | Vector(v, on) ->
    F.fprintf fmt "(make-list %i %a)" (Dimensions.width ())  base_value ()
  | _ -> base_value fmt ()



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
    let vi = mkFnVar "__MAX_INT_" Integer in
    pp_define_symbolic fmt (DefInteger [vi]);
    let input_symbols = input_symbols_of_vs input_vars in
    pp_loc_assert
      (F.pp_print_list
         ~pp_sep:(fun fmt () -> F.fprintf fmt "@;")
         (fun fmt inp_vi -> F.fprintf fmt "(< %s %s)" inp_vi.vname vi.vname))
      input_symbols;
    vi

  | NINFNTY ->
    let vi = mkFnVar "__MIN_INT_" Integer in
    pp_define_symbolic fmt (DefInteger [vi]);
    let input_symbols = input_symbols_of_vs input_vars in
    pp_loc_assert
      (F.pp_print_list
         ~pp_sep:(fun fmt () -> F.fprintf fmt "@;")
         (fun fmt inp_vi -> F.fprintf fmt "(> %s %s)" inp_vi.vname vi.vname))
      input_symbols;
    vi

let special_const_table : fnV IH.t = IH.create 10

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
       | FnConst NInfnty ->
         (** Assume all numeric inputs are greater than a symbolic variable.*)
         let vi = get_or_create fmt input_vars NINFNTY in
         FnVar (FnVariable vi)

       | FnConst Infnty ->
         let vi = get_or_create fmt input_vars INFNTY in
         FnVar (FnVariable vi)

       | _ -> expr) reach_consts



(** Pretty print the state structure with an equality predicate. The
    form of the definitions are defined in the Racket module.
*)
let defined_structs = SH.create 10

let define_structs fmt (rlist : fn_type list) =
  let define_struct fmt struct_name_and_fields =
  if SH.mem defined_structs (fst struct_name_and_fields) ||
     List.length (snd struct_name_and_fields) = 0
  then ()
  else
    begin
      SH.add defined_structs (fst struct_name_and_fields) (snd struct_name_and_fields);
      (pp_struct_definition ~transparent:true) fmt struct_name_and_fields;
      pp_newline fmt ();
      pp_struct_equality fmt struct_name_and_fields;
      pp_newline fmt ();
    end
  in
  List.iter
    (fun rt ->
       match rt with
       | Record(name, stl) ->
         define_struct fmt (name, fst(ListTools.unpair stl));
         fprintf fmt "@."

       | _ -> ()) rlist


(** Given a set of variables, pretty print their definitions and return
    a list of strings representing the names of the symbolic variables
    that have been defined.
    @param fmt A formatter.
    @param maxlines A integer representing the max number of symbolic matrix
    lines required for the problem.
    @param vars The set of variables whose defintion will be printed.
*)
let pp_symbolic_definitions_of ?(inner=false) fmt except_vars vars =
  pp_vs_to_symbs ~inner:inner fmt except_vars vars

(** Pretty print the body of the loop.
    @param loop_body The function representing the loop body.
    @param state_vars The set of state variables of this loop body.
    @param state_struct_name The name of the struct used to represent
    the state of the loop (valuation of the state variables).
*)

let pp_loop_body fmt (index_name, loop_body, state_vars) =
  let state_arg = mkFnVar (get_new_name ~base:"__s") (record_type state_vars) in
  let body_with_assigned_vars =
    FnLetIn(bind_state state_arg state_vars, loop_body)
  in
  Format.fprintf fmt "@[<hov 2>(lambda (%s %s)@;%a)@]"
    state_arg.vname
    index_name
    pp_fnexpr body_with_assigned_vars

(** Pretty print the whole loop wrapped in a Racket macro Loop and a function
    deifinition. The name of this function is set in the variable body_name of
    this module.
    @param loop_body The function representing the loop body.
    @param state_vars The set of state variables of this loop body.
    @param state_struct_name The name of the struct used to represent
    the state of the loop (valuation of the state variables).
*)
let pp_loop ?(inner=false) ?(dynamic=true) fmt index_set bnames (loop_body, state_vars)
    reach_const sname =
  let index_list = VarSet.elements index_set in
  if List.length index_list == 0 then
    failhere __FILE__ "pp_loop" "Only one index for the loop.";

  let index_name = (List.hd index_list).vname in
  let pp_index_low_up =
    (F.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
       (fun fmt vi ->
          let start_vi, end_vi = get_index_to_boundary vi in
          Format.fprintf fmt "%s %s" start_vi.vname end_vi.vname))
  in
  pp_comment fmt "Functional representation of the loop body.";
  (* Dynamic: both loop bounds can change. *)
  if dynamic then
    Format.fprintf fmt
      "@[<hov 2>(define (%s %s %a %a)@;\
       @[<hov 2>(Loop %a %d %s@;%a)@])@]@.@."
      body_name                   (* Name of the function *)
      (Conf.get_conf_string "rosette_state_param_name") (* Name of the input state *)
      pp_index_low_up index_list (* List of local lower and upper bounds - args *)
      pp_string_list bnames
      pp_index_low_up index_list (* List of local lower and upper bounds - loop *)
      (if inner then Dimensions.inner_iterations_limit else Dimensions.iterations_limit)
      (Conf.get_conf_string "rosette_state_param_name")
      pp_loop_body (index_name, loop_body, state_vars)


  else
    (* Else the start index is always fixed. *)
    let pp_index_up =
      (F.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
         (fun fmt vi ->
            let _, end_vi = get_index_to_boundary vi in
            Format.fprintf fmt "%s" end_vi.vname))
    in
    let extract_stv_or_reach_const, bound_state1 =
      let state_var_name = get_new_name ~base:(Conf.get_conf_string "rosette_state_param_name") in
      let state_var = mkFnVar state_var_name (record_type state_vars) in
      List.map
        (fun v ->
           if IM.mem v.vid reach_const then
             IM.find v.vid reach_const
           else
             FnApp(v.vtype, Some (record_accessor sname v),
                   [mkVarExpr state_var])) (VarSet.elements state_vars),
      state_var
    in
    (* Print the reaching constants (initialization of variables) *)
    pp_comment fmt "Sketch for the memoryless join: test for one instance.";
    Format.fprintf fmt
      "@[<hov 2>(define (%s %s %a)@;\
       @[<hov 2>(let ([%s (%s %a)])@;\
       @[<hov 2>(Loop %a %d %s@;%a)@])@])@]@.@."
      body_name                   (* Name of the function *)
      bound_state1.vname
      pp_index_up index_list
      (* Line 2: udpate state with constants, and bind it. *)
      bound_state1.vname
      sname
      pp_expr_list extract_stv_or_reach_const
      (* Line 3: loop construct and loop body. *)
      pp_index_low_up index_list (* List of local lower and upper bounds - loop *)
      (if inner then Dimensions.inner_iterations_limit else Dimensions.iterations_limit)
      bound_state1.vname
      pp_loop_body (index_name, loop_body, state_vars)



(** Pretty print the body of the join function in the Rosette sketch.
    @param join_body The function of the join.
    @param state_vars The set of state variables.
    @param lstate_name The name of the left state argument of the join.
    @param rstate_name The name of the right state argument of the join.
*)
let pp_join_body fmt (join_body, state_vars, lstate, rstate) =
  let lpref = Conf.get_conf_string "rosette_join_left_state_prefix" in
  let rpref = Conf.get_conf_string "rosette_join_right_state_prefix" in
  let body_with_bound_vars =
    FnLetIn(
      bind_state ~prefix:lpref ~state_rec:lstate ~members:state_vars,
      FnLetIn(
        bind_state ~prefix:rpref ~state_rec:rstate ~members:state_vars,
        join_body))
  in
  printing_sketch := true;
  pp_fnexpr fmt body_with_bound_vars;
  printing_sketch := false


(** Pretty print the join function using the body pretty printing function
    wrapped in a defintion. The name of the function is defined in the
    join_name variable in the module.
    @param join_body The function of the join.
    @param state_vars The set of state variables.
*)
let pp_join fmt (inner, sketch) =
  let lstate_name = Conf.get_conf_string "rosette_join_left_state_name" in
  let rstate_name = Conf.get_conf_string "rosette_join_right_state_name" in
  let state_vars = sketch.scontext.state_vars in
  let stype = record_type state_vars in
  let lstate = mkFnVar (get_new_name ~base:lstate_name) stype in
  let rstate = mkFnVar (get_new_name ~base:rstate_name) stype in
  let ist, ien = get_bounds sketch in
  let jbody =
    if inner then sketch.memless_sketch else sketch.join_sketch
  in
  define_structs fmt (used_struct_types jbody);
  pp_comment fmt  "-------------------------------";
  Format.fprintf fmt
    "@[<hov 2>(define (%s %s %s %s %s)@;%a)@]@.@."
    join_name  lstate.vname rstate.vname ist.vname ien.vname
    pp_join_body (jbody, state_vars, lstate, rstate)

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
let pp_states ?(dynamic=true) fmt state_vars read_vars st0 reach_consts =
  let struct_name = record_name state_vars in
  let reach_consts = handle_special_consts fmt read_vars reach_consts in
  let identity_state_sketch =
    F.pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
      (fun fmt vi ->
         Format.fprintf fmt "%a" base_init_value_choice (reach_consts, vi))
  in
  (** Pretty print the identity state, with holes *)
  Format.fprintf fmt
    "@[(define %s (%s %a))@]@."
    ident_state_name
    struct_name
    identity_state_sketch (VarSet.elements state_vars);

  (** Handle special constants such as Infnty and NInfnty to create the
      necessary assertions and symbolic variables *)

  (** Pretty print the initial states, with reaching constants and holes
      for the auxiliaries discovered *)
  if dynamic then
    Format.fprintf fmt
      "@[(define (%s %s %s) (%s %a))@]@."
      st0
      "_begin_" "end"
      struct_name
      (fun fmt li ->
         (ppli fmt ~sep:" "
            (fun fmt (vid, vi) ->
               (if IM.mem vid reach_consts
                then
                  let var_begin = {vi with vname = "_begin_"} in
                  register_fnv var_begin;
                  pp_fnexpr fmt
                    (try
                       replace_all_subs
                         ~tr:[FnConst (CInt 0); FnConst (CInt64 0L)]
                         ~by:[mkVarExpr var_begin; mkVarExpr var_begin]
                         ~ine:(IM.find vid reach_consts)
                     with _ -> IM.find vid reach_consts)
                else
                  (* (if IH.mem auxiliary_vars vid
                   *  then *)
                  Format.fprintf fmt "%a"
                    base_init_value_choice (reach_consts, vi)
                    (* else
                     *   begin
                     *     F.eprintf
                     *       "@.%sERROR : \
                     *        Variable %s should be initialized or auxiliary.%s@."
                     *       (color "red") vi.vname color_default;
                     *     failhere __FILE__ "pp_state" "(See ERROR) Unexpected variable."
                     *   end )*)
               )))
           li)
      (VarSet.bindings state_vars)
  else
    Format.fprintf fmt
      "@[(define (%s %s) (%s %a))@]@."
      st0
      "end_index"
      struct_name
      (fun fmt li ->
         (ppli fmt ~sep:" "
            (fun fmt (vid, vi) ->
               (if IM.mem vid reach_consts
                then
                  pp_fnexpr fmt (IM.find vid reach_consts)
                else
                  (if IH.mem auxiliary_vars vid
                   then
                     Format.fprintf fmt "%a"
                       base_init_value_choice (reach_consts, vi)
                   else
                     begin
                       F.eprintf
                         "@.%sERROR : \
                          Variable %s should be initialized or auxiliary.%s@."
                         (color "red") vi.vname color_default;
                       failwith "Unexpected variable."
                     end))))
           li)
      (VarSet.bindings state_vars)


let pp_input_state_definitions ?(inner=false) fmt state_vars reach_consts =
  let s0_sketch_printer =
    F.pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
      (fun fmt vi ->
         Format.fprintf fmt "%a" base_init_value_choice (reach_consts, vi))
  in
  (* Sketch for the identity state. *)
  (** Pretty print the identity state, with holes *)
  Format.fprintf fmt
    "@[(define (%s %s) (%s %a))@]@."
    ident_state_name "iEnd"
    (record_name state_vars)
    s0_sketch_printer (VarSet.elements state_vars);
  (* Define the symbols that do not have reaching consts.*)
  let symbolic_vars = (VarSet.add_prefix state_vars "symbolic_") in
  pp_symbolic_definitions_of ~inner:inner fmt [] symbolic_vars;
  Format.fprintf fmt
    "@[(define (%s %s) (%s %a))@]@."
    init_state_name "iEnd"
    (record_name state_vars)
    pp_expr_list (List.map mkVarExpr (VarSet.elements symbolic_vars));
  symbolic_vars


(** Pretty print the whole body of the synthesis problem. (The set of
    verification conditions is hardcoded here now, we have to change that).
    @param s0 The name of the initial state.
    @param state_vars The set of state variables.
    @param symbolic_variable_names The list of symbolic variable names that will
    have a universal quantifier over.
*)
let pp_synth_body ?(m=false) fmt (s0, bnm, struct_name, defined_input_vars, min_dep_len) =
  let pp_join_verification_condition fmt struct_name (s0, bnm, i_st, i_m, i_end) min_dep_len =
    let bnds = (bnm, i_st, i_m, i_end) in
    if i_m - i_st >= min_dep_len && i_end - i_m >= min_dep_len then
      Format.fprintf fmt
        "@[<hov 2>(%s-eq?@;%a@;(%s %a %a %d %d))@]"
        struct_name
        pp_join_body_app (body_name, s0, bnds, i_st, i_end)
        join_name
        pp_join_body_app (body_name, s0, bnds, i_st, i_m)
        pp_join_body_app (body_name, init_state_name, bnds, i_m, i_end)
        i_st
        i_end
    else
      ()
  in

  let pp_mless_verification_condition fmt struct_name (s0, bnm, i_st, i_m, i_end) min_dep_len =
    if i_m - i_st >= min_dep_len && i_end - i_m >= min_dep_len
       && i_end <= Dimensions.inner_iterations_limit
    then
      Format.fprintf fmt
        "@[<hov 2>(%s-eq?@;%a@;(%s (%s %d) %a 0 %d))@]"
        struct_name
        pp_mless_body_app (body_name, init_state_name, i_end)
        join_name
        init_state_name i_end
        pp_mless_body_app (body_name, s0, i_end)
        i_end
    else
      ()
  in
  Format.fprintf fmt
    "@[<hov 2>#:forall @[<hov 2>(list %a)@]@]@\n"
    pp_defined_input defined_input_vars;
  if m then
    Format.fprintf fmt
      "@[<hov 2>#:guarantee @[(assert@;(and@;%a))@]@]"
      (F.pp_print_list
         (fun fmt (i_st, i_m, i_end) ->
            pp_mless_verification_condition fmt struct_name (s0, bnm, i_st, i_m, i_end)
              min_dep_len))
      Conf.verification_parameters
  else
    Format.fprintf fmt
      "@[<hov 2>#:guarantee @[(assert@;(and@;%a))@]@]"
      (F.pp_print_list
         (fun fmt (i_st, i_m, i_end) ->
            pp_join_verification_condition fmt struct_name (s0, bnm, i_st, i_m, i_end)
              min_dep_len))
      Conf.verification_parameters


(** Pretty-print a synthesis problem wrapped in a defintion for further
    access to the solved problem
*)
let pp_synth ?(memoryless=false) fmt s0 bnames state_vars pb_input_vars min_dep_len =
  Format.fprintf fmt
    "@[<hov 2>(define odot (synthesize@;%a))@.@."
    (pp_synth_body ~m:memoryless) (s0, bnames, state_vars, pb_input_vars, min_dep_len)


(* ---------------------------------------------------------------------------- *)
(* When there are inner loops, those have been replaced by function calls in the
   outer body. We need to define the corresponding functions *)
let define_inner_join fmt lname (state, styp) (ist, iend) join =
  let lstate_var = mkFnVar "$L" styp in
  let rstate_var = mkFnVar "$R" styp in
  let bind_lstate = bind_state ~prefix:left_state_prefix ~state_rec:lstate_var ~members:state in
  let bind_rstate = bind_state ~prefix:right_state_prefix ~state_rec:rstate_var ~members:state in
  let wrapped_join =
    FnLetIn (bind_lstate@bind_rstate, join)
  in
  fprintf fmt "@[<v 2>(define (%s %s %s %s %s)@;%a)@]"
    (Conf.join_name lname)
    lstate_var.vname
    rstate_var.vname
    ist.vname
    iend.vname
    pp_fnexpr wrapped_join

let pp_inner_def fmt pb =
  (* Define state struct type. *)
  pp_comment fmt "Defining struct for state of the inner loop.";
  define_structs fmt (used_struct_types pb.main_loop_body);
  pp_newline fmt ()

let pp_inner_loops_defs fmt inner_loop_list =
  match inner_loop_list with
  | [] -> ()
  | _ -> List.iter (pp_inner_def fmt) inner_loop_list

let pp_inner_join_def fmt pb =
  let stv = pb.scontext.state_vars in
  let styp = record_type stv in
  pp_comment fmt "Defining inner join function for outer loop.";
  define_inner_join
    fmt pb.loop_name (stv, styp) (get_bounds pb) pb.memless_solution;
  pp_newline fmt ()

let pp_inner_loops_joins fmt inner_loop_list =
  match inner_loop_list with
  | [] -> ()
  | _ -> List.iter (pp_inner_join_def fmt) inner_loop_list



(* ---------------------------------------------------------------------------- *)
(* Specific to pretty printing the sketch for the memoryless join. *)
let pp_static_loop_bounds fmt index_name =
  Format.fprintf fmt
    "(define %s%s %i)@."
    index_name index_begin 0

(** Pretty print the whole body of the synthesis problem. (The set of
    verification conditions is hardcoded here now, we have to change that).
    @param s0 The name of the initial state.
    @param state_vars The set of state variables.
    @param symbolic_variable_names The list of symbolic variable names that will
    have a universal quantifier over.
*)

let pp_rosette_sketch_inner_join fmt parent_context sketch =
  clear_special_consts ();
  SH.clear defined_structs;
  let min_dep_len = sketch.min_input_size in
  (** State variables *)
  let state_vars = sketch.scontext.state_vars in
  (** Read variables : force read /\ state = empty *)
  let read_vars =
    VarSet.diff
      (remove_interpreted_symbols sketch.scontext.used_vars)
      (VarSet.union state_vars sketch.scontext.index_vars)
  in
  let idx = sketch.scontext.index_vars in
  let index_name = (VarSet.max_elt idx).vname in
  let parent_index_var = (VarSet.max_elt (parent_context.index_vars)) in
  let repl_par_idx e =
        replace_expression
      ~in_subscripts:true
      ~to_replace:(FnVar (FnVariable parent_index_var))
      ~by:(FnConst (CInt 0))
      ~ine:e
  in
  let st0 = ident_state_name in
  (* Global bound name "n" *)
  let bnd_vars =
    List.fold_left
      (fun name_list expr ->
         match expr with
         | Some (FnVar (FnVariable vi)) -> name_list@[vi]
         | _ -> name_list)
      []
      (if sketch.uses_global_bound then
         [(get_loop_bound sketch)]
       else [])
  in
  let bnames =
    List.map (fun vi -> vi.vname) bnd_vars
  in
  let struct_name = record_name state_vars in
  (* The parent index has to be replaced with a constant. *)
  let loop_body = repl_par_idx sketch.main_loop_body in
  let rconsts = IM.map repl_par_idx sketch.reaching_consts in
  let input_struct_types =
    List.filter
      (fun vtype -> match vtype with Record _ -> true | _ -> false)
      (List.map (fun var -> match var.vtype with
           | Record (nm, l) ->  Record (nm, l)
           | Vector(Record (nm,l), _) -> Record (nm,l)
           | t -> t)
          (VarSet.elements read_vars))
  in
  (* Select the bitwidth for representatin in Rosettte depending on the
     operators used in the loop body. *)
  pp_current_bitwidth fmt sketch.main_loop_body;

  define_structs fmt (used_struct_types sketch.main_loop_body);
  define_structs fmt (used_struct_types sketch.memless_sketch);
  define_structs fmt (used_struct_types sketch.join_sketch);
  define_structs fmt input_struct_types;
  (**
     Print all the necessary symbolic definitions. For the memoryless join,
     we need only one line of matrix input.
  *)
  pp_symbolic_definitions_of fmt bnd_vars (VarSet.diff read_vars state_vars);
  pp_newline fmt ();
  pp_newline fmt ();
  pp_static_loop_bounds fmt index_name;
  pp_newline fmt ();
  pp_loop ~inner:true ~dynamic:false fmt idx bnames (loop_body, state_vars)
    rconsts struct_name;
  pp_comment fmt "Wrapping for the sketch of the memoryless join.";
  pp_join fmt (true, sketch);
  pp_newline fmt ();
  pp_comment fmt "Symbolic input state and synthesized id state";
  let additional_symbols =
    pp_input_state_definitions ~inner:true fmt state_vars rconsts
  in
  pp_comment fmt "Actual synthesis work happens here";
  pp_newline fmt ();
  pp_synth ~memoryless:true fmt st0 bnames struct_name
    (VarSet.union read_vars additional_symbols)
    (* (VarSet.union read_vars additional_symbols) *)
    min_dep_len


let pp_rosette_sketch_join fmt sketch =
  clear_special_consts ();
  SH.clear defined_structs;
  let min_dep_len = sketch.min_input_size in
  (** State variables *)
  let state_vars = sketch.scontext.state_vars in
  let struct_name = record_name state_vars in
  (** Read variables : force read /\ state = empty *)
  let read_vars =
    VarSet.diff
      (remove_interpreted_symbols sketch.scontext.used_vars)
      (VarSet.union state_vars sketch.scontext.index_vars)
  in
  let idx = sketch.scontext.index_vars in
  let st0 = init_state_name in
  (* Global bound name "n" *)
  let bnd_vars =
    List.fold_left
      (fun name_list expr ->
         match expr with
         | Some (FnVar (FnVariable vi)) -> name_list@[vi]
         | _ -> name_list)
      []
      (if sketch.uses_global_bound then
         [(get_loop_bound sketch)]
       else [])
  in
  let bnames =
    List.map (fun vi -> vi.vname) bnd_vars
  in
  let lbody =
    List.fold_left
      (fun lbody inner_loop ->
         let i_st, i_end = get_bounds inner_loop in
         let rep1 =
           replace_expression
             ~in_subscripts:true
             ~to_replace:(mkVarExpr i_st)
             ~by:(FnConst (CInt 0))
             ~ine:lbody
         in
         replace_expression
           ~in_subscripts:true
           ~to_replace:(mkVarExpr i_end)
           ~by:(FnConst (CInt (Dimensions.width ())))
           ~ine:rep1
      )
      sketch.main_loop_body
      sketch.inner_functions
  in
  let input_struct_types =
    List.filter
      (fun vtype -> match vtype with Record _ -> true | _ -> false)
      (List.map (fun var -> match var.vtype with
           | Record (nm, l) ->  Record (nm, l)
           | Vector(Record (nm,l), _) -> Record (nm,l)
           | t -> t)
          (VarSet.elements read_vars))
  in
  (** FPretty configuration for the current sketch *)
  pp_current_bitwidth fmt sketch.main_loop_body;

  define_structs fmt (used_struct_types sketch.main_loop_body);
  define_structs fmt (used_struct_types sketch.memless_sketch);
  define_structs fmt input_struct_types;

  if List.length sketch.inner_functions > 0 then
    begin
      pp_inner_loops_defs fmt sketch.inner_functions;
      pp_newline fmt ()
    end;
  pp_symbolic_definitions_of fmt bnd_vars read_vars;
  pp_newline fmt ();
  define_structs fmt (used_struct_types sketch.main_loop_body);
  pp_newline fmt ();
  if List.length sketch.inner_functions > 0 &&
     InnerFuncs.uses_inner_join_func sketch.main_loop_body
  then
    begin
      pp_inner_loops_joins fmt sketch.inner_functions;
      pp_newline fmt ()
    end;
  pp_newline fmt ();
  pp_loop fmt idx bnames (lbody, state_vars) sketch.reaching_consts struct_name;
  pp_comment fmt "Wrapping for the sketch of the join.";
  pp_join fmt (false, sketch);
  pp_newline fmt ();
  pp_comment fmt "Symbolic input state and synthesized id state";
  pp_states fmt state_vars read_vars st0 sketch.reaching_consts;
  pp_comment fmt "Actual synthesis work happens here";
  pp_newline fmt ();
  pp_synth fmt st0 bnames struct_name read_vars min_dep_len


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
let pp_rosette_sketch parent_context inner fmt (sketch : prob_rep) =
  if inner then
    pp_rosette_sketch_inner_join fmt parent_context sketch
  else
    pp_rosette_sketch_join fmt sketch


(******************************************************************************)

(** 1 - SYNTHLIB
    Compile the Synthlib sketch.
*)

(** TODO
    Returns the logic needed to solve the sketch.
*)
let logic_of_pb pb = SyLIA

(* There are no comp types in synthlib. *)
let funcdef_body pb =
  let ret_sort =
    (List.map (fun x -> sort_of_ciltyp (check_option (ciltyp_of_symb_type x)))
       (VarSet.types pb.scontext.state_vars))
  in
  let funbody = SyLiteral (SyInt 0)
  in
  SyFunDefCmd (pb.loop_name, [], List.hd ret_sort, funbody)

let pp_synthlib_problem fmt (pb : prob_rep) =
  (* Declare the logic to use *)
  fprintf fmt "%a@." sypp_logic (logic_of_pb pb);
  (* The function. *)
  fprintf fmt "%a@." sypp_command (funcdef_body pb);
