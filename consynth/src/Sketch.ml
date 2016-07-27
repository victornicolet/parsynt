open Utils
open Format
open Core.Std
open Utils
open SketchTypes
open SPretty
open PpHelper
open Cil2Func
open Join
open Racket

module VS = VS
module SM = Map.Make (String)
module Ct = CilTools

let debug = ref false;;
let iterations_limit = ref "10"
(**
   The main entry point of the file is build_sketch :
   build a sketch from the Floop (vector of functions
   for each state variable representing the ody of the
   loop).
*)

let rec convert (cur_v : skLVar) =
  function
  | Var vi -> mkVar vi

  (** TODO : array -> region *)
  | Array (vi, el) ->
     let skexpr_list = List.map el ~f:(convert cur_v) in
     mkVar ~offsets:skexpr_list vi

  | FunApp (ef, arg_l) ->
     let is_c_def, vi_o, ty = is_exp_function ef in
     let sty = symb_type_of_ciltyp ty in
     let fargs =  List.map arg_l ~f:(convert cur_v) in
     if is_c_def then
       SkApp (sty, vi_o, fargs)
     else
       let fname = (checkOption vi_o).Cil.vname in
       (match fargs with
       | [e] ->
          let unop = (checkOption (symb_unop_of_fname fname)) in
          SkUnop (unop, e)
       | e1::[e2] ->
          let binop = (checkOption (symb_binop_of_fname fname)) in
          SkBinop (binop, e1, e2)
       | _ -> SkApp (sty, vi_o, fargs))


  | Container (e, subs) ->
     let converted_substitutions = IM.map (convert cur_v) subs in
     convert_cils ~cur_v:cur_v ~subs:converted_substitutions e

  | FQuestion (ecil, e1, e2) ->
     SkQuestion (convert_cils ecil, (convert cur_v e1), (convert cur_v e2))

  | FRec ((i, g, u), expr) ->
     SkRec ((i, g, u), SkLetExpr [(cur_v, convert cur_v expr)])

  | FBinop (op, e1, e2) ->
     SkBinop (op, convert cur_v e1, convert cur_v e2)

  | FUnop (op, e) -> SkUnop (op, convert cur_v e)

  | FConst c -> SkConst c

  | FSizeof t -> SkSizeof (symb_type_of_ciltyp t)
  | FSizeofE e -> SkSizeofE (convert cur_v e)
  | FSizeofStr s -> SkSizeofStr s
  | FAlignof t -> SkAlignof (symb_type_of_ciltyp t)
  | FAlignofE e -> SkAlignofE (convert cur_v e)
  | FCastE (t, e) -> SkCastE (symb_type_of_ciltyp t, convert cur_v e)
  | FAddrof lval -> SkAddrof (skexpr_of_lval cur_v lval)
  | _ -> failwith "not yet implemented"


and convert_cils ?(cur_v = SkState) ?(subs = IM.empty) =
  function
  | Cil.Const c -> skexpr_of_constant c

  | Cil.Lval v ->
     let skvar = skexpr_of_lval cur_v v in
     begin
       match skvar with
       | SkVar (SkVarinfo vi) when IM.mem vi.Cil.vid subs ->
          IM.find vi.Cil.vid subs
       | _ ->skvar
     end

  | Cil.SizeOf t->
     let typ = symb_type_of_ciltyp t in
     SkSizeof typ

  | Cil.SizeOfE e ->
     SkSizeofE (convert_cils ~subs:subs e)

  | Cil.SizeOfStr s ->
     SkSizeofStr s

  | Cil.AlignOf t ->
     SkAlignof (symb_type_of_ciltyp t)

  | Cil.AlignOfE e ->
     SkAlignofE (convert_cils ~subs:subs e)

  | Cil.AddrOf lv ->
     SkAddrof (skexpr_of_lval cur_v lv)

  | Cil.AddrOfLabel stm_ref ->
     SkAddrofLabel stm_ref

  | Cil.UnOp (op, e1, t) ->
     let op' = symb_unop_of_cil op in
     SkUnop (op',convert_cils ~subs:subs e1)

  | Cil.BinOp (op, e1, e2, t) ->
     let op' = symb_binop_of_cil op in
     SkBinop (op', convert_cils ~subs:subs e1, convert_cils ~subs:subs e2)

  | Cil.Question (c, e1, e2, t) ->
     let c' = convert_cils c in
     SkQuestion (c',  convert_cils ~subs:subs e1, convert_cils ~subs:subs e2)

  | Cil.CastE (t, e) ->
     SkCastE (symb_type_of_ciltyp t, convert_cils ~subs:subs e)

  | Cil.StartOf lv ->
     SkStartOf (skexpr_of_lval cur_v lv)


and convert_offset =
  function
  | Cil.NoOffset -> []
  | Cil.Index (e, offset) ->
     ((convert_cils e)::(convert_offset offset))
  | Cil.Field _ -> []

and convert_offsets offsets_list =
  List.fold_left offsets_list
    ~init:[]
    ~f:(fun acc x -> acc@(convert_offset x))


and skexpr_of_lval (cur_v : skLVar)
    ((host, offset) : Cil.lval) =
  match convert_offset offset with
  (**
      A null list only means there is no offset in the offset part
      of the Cil.lval, but the offset might still in the expression
      if it is a Cil memory access.
  *)
  | [] ->
     let vo, ofs_li = CilTools.get_host_var host in
     begin
       match vo with
       | Some vi ->
          mkVar ~offsets:(convert_offsets ofs_li) vi
       | None -> failwith "Is it an lval ?"
     end

  | new_off_list ->
       let vo, prev_offs_list =  CilTools.get_host_var host in
       let off_list = (convert_offsets prev_offs_list)@new_off_list in
       let vi_to_expr =
         match vo with
         | None ->
          (** Anonymous function with type *)
            (fun t x -> SkApp (t, None, off_list))
         | Some vi ->
            (fun t x -> x vi)
       in
       let t =  Cil.typeOfLval (host,offset) in
       vi_to_expr
         (symb_type_of_ciltyp t)
         (mkVar ~offsets:off_list)


and skexpr_of_constant c =
  let const =  match c with
    | Cil.CInt64 (i, ik, stro) ->
       if Ct.is_like_bool ik then CBool (Ct.bool_of_int64 i)
       else CInt64 i
    | Cil.CReal (f, fk, stro) ->
       CReal f
    | Cil.CChr cr ->
       CChar cr
    | Cil.CStr s ->
       CString s
    | _ -> CBox c
  in SkConst const

(** TODO : add the current loop index *)
and convert_letin (vs : VS.t) =
  function
    | State subs  ->
       let state =
         List.map (IM.bindings subs)
            ~f:(fun (k,e) ->
              let cur_v = SkVarinfo (VSOps.getVi k vs) in
                                    (cur_v, convert cur_v e))
              in
       let complete_state =
         state@(List.map
                  (VSOps.varlist
                     (VS.filter (fun v -> not (IM.mem v.Cil.vid subs)) vs))
                  ~f:(fun vi -> (SkVarinfo vi, mkVar vi)))
       in
       SkLetExpr complete_state

    | Let (v, e, cont, i, loc) ->
       let cur_v = SkVarinfo v in
       SkLetIn ([(cur_v, convert cur_v e)], convert_letin vs cont)

    | LetRec (igu, let_body, let_cont, loc) ->
       (** Tail position *)
       if is_empty_state let_cont then
         SkLetExpr [(SkState, SkRec (igu, convert_letin vs let_body))]
       else
         SkLetIn ([(SkState, SkRec (igu, convert_letin vs let_body))],
                  convert_letin vs let_cont)

    | LetCond (c, let_if, let_else, let_cont, loc) ->
       if is_empty_state let_cont then
         SkLetExpr [(SkState,
                     SkCond (convert_cils c,
                             convert_letin vs let_if,
                             convert_letin vs let_else))]
       else
          SkLetIn ( [(SkState,
                     SkCond (convert_cils c,
                             convert_letin vs let_if,
                             convert_letin vs let_else))],
                  convert_letin vs let_cont)
    | LetState (let_state, let_cont) ->
       SkLetIn ([(SkState, SkFun (convert_letin vs let_state))],
                convert_letin vs let_cont)

(** Optimisations *)
let remove_simple_state_rewritings (var , expr) =
  match var, expr with
  | SkState, SkFun (SkLetExpr li) ->
     begin
       match List.filter li
         ~f:(fun e -> match e with _, SkVar _ -> false |_, _-> true)
       with
       | [(v, e)] -> v, e
       | _ -> (var, expr)
     end
  | _ -> (var, expr)

let optims sklet =
  match sklet with
  | SkLetExpr el -> sklet
  | SkLetIn (el, cont) ->
     let new_rewrites = List.map el ~f:remove_simple_state_rewritings in
     SkLetIn (new_rewrites, cont)


(*** MAIN ENTRY POINT ***)

let build_body (let_form : letin) (state : VS.t) =
  optims (convert_letin state let_form)

let build_join (sklet : sklet) (state : VS.t) =
  make_join state sklet

(** Transform the converted sketch to a loop body and a join sketch *)

let rec make_conditional_guards (initial_vs : VS.t) (letin_form : sklet) =
  match letin_form with
  | SkLetIn (bindings, body) ->
	let new_bindings, new_state_vars = mk_cg bindings initial_vs in
	let new_body, state_vars' = make_conditional_guards new_state_vars body in
	SkLetIn (new_bindings, new_body), state_vars'

  | SkLetExpr bindings ->
	let new_bindings, new_state_vars = mk_cg bindings initial_vs in
	SkLetExpr new_bindings, new_state_vars

and mk_cg bindings vs =
  (List.fold
	bindings
	~init: []
	~f:(fun acc binding -> acc @ [mk_cg_binding vs binding])), vs

and mk_cg_binding vs ((var, expr) : skLVar * skExpr) =
  (var, expr)


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

let pp_symbDef fmt sd =
  let fp = Format.fprintf in
  match sd with
  | Integers li ->
     fp fmt "(define-symbolic %a integer?)" pp_string_list li
  | Reals li ->
     fp fmt "(define-symbolic %a real?)" pp_string_list li
  | Booleans li ->
     fp fmt "(define-symbolic %a boolean?)" pp_string_list li
  | RoArray (sty, varnames) ->
     fp fmt "(define-symbolic %a (~> integer? %s))" pp_string_list varnames sty

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


let defsRec_to_symbDefs defs_rec
    : (symbDef * symbDef * symbDef * (symbDef list) ) =
  let ro_arrays_map =
    List.fold_left
      defs_rec.vecs
      ~init:SM.empty
      ~f:(fun tmap (vname, sty) ->
        SM.update tmap sty
          (function
          | Some l -> vname::l
          | None -> [vname] ))
  in
  let ro_arrays = SM.to_alist ro_arrays_map in
  let roArrays = List.map  ro_arrays ~f:(fun (k,v) -> RoArray (k, v))
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
let main_struct_name = "__state"

let pp_state_definition fmt main_struct =
  pp_struct_defintion fmt main_struct;
  pp_force_newline fmt ();
  pp_struct_equality fmt main_struct


let pp_ne_symbdefs fmt sd =
  if is_empty_symbDefs sd
  then Format.fprintf fmt ""
  else
    begin
      Format.fprintf fmt "@[<hov 0>@.%a@]@."
        pp_symbDef sd
    end

let strings_of_symbdefs symbdef =
  pp_ne_symbdefs str_formatter symbdef; flush_str_formatter ()


let pp_symbolic_definitions_of fmt vars =
  let (ints, reals, booleans, arrays)
      = defsRec_to_symbDefs (defsRec_of_varinfos vars) in
  Format.fprintf fmt
    "%a%a%a%a@."
    pp_ne_symbdefs ints
    pp_ne_symbdefs reals
    pp_ne_symbdefs booleans
    (pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt "@.")
       (fun fmt sd -> pp_ne_symbdefs fmt sd))
    arrays


(** Loop body *)
let pp_assignments state_struct_name state_name fmt =
  pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt "@;")
    (fun fmt s -> Format.fprintf fmt "[%s (%s-%s %s)]"
      s state_struct_name s state_name) fmt

let pp_loop_body fmt (loop_body, state_vars, state_struct_name) =
 let field_names =
    List.map (VSOps.varlist state_vars) ~f:(fun vi -> vi.Cil.vname) in
  Format.fprintf fmt "(lambda (s i) @[<hov 2>(let@;(%a) %a)@])"
    (pp_assignments state_struct_name "s") field_names
    pp_sklet loop_body

let pp_loop fmt (loop_body, state_vars) state_struct_name =
  Format.fprintf fmt
    "(define (body s start end)@; \
@[<hov 2>(Loop  @[<hov 4> start end  %s s@] @.\
@[<hov 4> %a@])@])@."
    !iterations_limit
    pp_loop_body (loop_body, state_vars, state_struct_name)


let pp_join fmt (join_body, state_vars) =
  let left_state_vars = VSOps.vs_with_suffix state_vars "-left" in
  let right_state_vars = VSOps.vs_with_suffix state_vars "-right" in
  set_hole_vars left_state_vars right_state_vars;
  Format.fprintf fmt
    "(define join @[<hov 2>(LamJoin (%a) (%a) @;@[<hov 4>%a@])@])@."
    VSOps.pp_var_names left_state_vars
    VSOps.pp_var_names right_state_vars
    pp_sklet join_body


let pp_states fmt state_vars read_vars st1 st2 st0 =
  set_hole_vars read_vars read_vars;
  let s0_sketch_printer =
    pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
      (fun fmt vi ->
        let t = symb_type_of_ciltyp vi.Cil.vtype in
        let hole = SkHoleR t in
        Format.fprintf fmt "%a" pp_skexpr hole)
  in
  Format.fprintf fmt
    "@[(define %s (%s %a))@]"
    st0 main_struct_name
    s0_sketch_printer (VSOps.varlist state_vars);

  let st1_vars = VSOps.vs_with_suffix state_vars "1" in
  let st2_vars = VSOps.vs_with_suffix state_vars "2" in
  pp_symbolic_definitions_of fmt st1_vars;
  pp_symbolic_definitions_of fmt st2_vars;
  Format.fprintf fmt
    "@[(define %s (%s %a))@]@.@[(define %s (%s %a))@]@."
    st1
    main_struct_name
    VSOps.pp_var_names st1_vars
    st2
    main_struct_name
    VSOps.pp_var_names st2_vars


let pp_synth fmt s1 s2 s0 state_vars =
  Format.fprintf fmt
    "@[(define odot@;@[<hov 2>(Synthesize %s %s %s (%a))@])@]@."
    s1 s2 s0
    VSOps.pp_var_names state_vars


let pp_rosette_sketch fmt (read_vars, state, all_vars, loop_body, join_body) =
  let state_vars = VSOps.subset_of_list state all_vars in
  let read_vars = VSOps.subset_of_list read_vars all_vars in
  let field_names =
    List.map (VSOps.varlist state_vars) ~f:(fun vi -> vi.Cil.vname) in
  let main_struct = (main_struct_name, field_names) in
  let st1, st2, st0 = "state1", "state2", "init-state" in
  (** SPretty configuration for the current sketch *)
  SPretty.read_only_arrays := read_vars;
  SPretty.state_struct_name := main_struct_name;
  pp_symbolic_definitions_of fmt read_vars;
  pp_force_newline fmt ();
  pp_state_definition fmt main_struct;
  pp_force_newline fmt ();
  pp_loop fmt (loop_body, state_vars) main_struct_name;
  pp_join fmt (join_body, state_vars);
  pp_force_newline fmt ();
  pp_states fmt state_vars read_vars st1 st2 st0;
  pp_synth fmt st1 st2 st0 state_vars
