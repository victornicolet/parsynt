open Base
open Fmt
open Lang.SolutionDescriptors
open Lang.Term
open Lang.TermPp
open Lang.Typ
open Predefs
open Utils
module OC = Stdio.Out_channel

let oplus_name = "$oplus"

let init_name = "$s$0"

let infer_divisions (_ : eqs_soln_info) =
  let list_len = !Config.sl_join_synt_len in
  if list_len > 4 then ListTools.(2 -- (list_len - 2))
  else (
    (* Probably too short, shouldn't bet set so low. *)
    Log.error (wrap "Parameter sl_join_syn_len in Config.ml is too small.");
    failwith "Bad parameter." )

let im_to_fields (sinfo : eqs_soln_info) (im : (int, 'a, 'b) Base.Map.t) : (string * 'a) list =
  let f v = (v.vname, Map.find_exn im v.vid) in
  List.map ~f (Set.to_list sinfo.func_info.vars)

let pp_input_defs (_ : eqs_soln_info) (_ : Formatter.t) = ()

let pp_struct_defs (si : eqs_soln_info) (fout : Formatter.t) =
  let s, fields = VarSet.to_struct si.func_info.vars in
  let used_structs =
    Lang.Analyze.used_structs
      (mk_list (List.map ~f:(fun (_, eqn) -> eqn.erhs) (Map.to_alist si.func_info.eqns)))
  in
  pre_pp_struct_defs fout (Set.add used_structs (TStruct (s, fields)))

let pp_orig_func_def (sinfo : eqs_soln_info) (fout : Formatter.t) =
  let structed_body =
    mk_struct
      (List.map
         ~f:(fun (fn, t) -> (fn, subs_state_v sinfo.func_info t.erhs))
         (im_to_fields sinfo sinfo.func_info.eqns))
  in
  let structed_init =
    mk_struct (List.map ~f:(fun (fn, e) -> (fn, e.einit)) (im_to_fields sinfo sinfo.func_info.eqns))
  in
  (* Define initial state / term of fold. *)
  pf fout "@[<v 2>(define (%s@;%a) %a)@]@." sinfo.init_name VarSet.pp_var_names
    sinfo.func_info.collection_inputs rpp_term structed_init;
  (* Define oplus. *)
  pf fout "@[<v 2>(define (%s %s %s)@;%a)@]@." oplus_name sinfo.func_info.x.vname
    sinfo.func_info.lstate.vname rpp_term structed_body;
  pp_newline fout ();
  (* Define fold. *)
  pf fout "@[<v 2>(define (%s %a)@;@[<v 2>(foldl@;%s@;(%s@;%a)@;%a)@])@]@." sinfo.func_name
    VarSet.pp_var_names sinfo.func_info.collection_inputs oplus_name sinfo.init_name
    VarSet.pp_var_names sinfo.func_info.collection_inputs VarSet.pp_var_names
    sinfo.func_info.collection_inputs

let pp_join (relevant_fields : string list option) (sinfo : eqs_soln_info) (fout : Formatter.t) :
    unit =
  let placeholder t = match t with TInt -> mk_int 0 | TBool -> mk_true | _ -> mk_int 0 in
  let pick_one_join fn jt =
    match jt.ejoin with
    | Either.First soln -> subs_state_v sinfo.func_info soln
    | Second _ -> (
        match relevant_fields with
        | Some fns ->
            if List.mem fns ~equal:String.equal fn then Sketching.make sinfo fn
            else placeholder jt.einit.ttyp
        | None -> Sketching.make sinfo fn )
  in
  let join_body =
    mk_struct
      (List.map
         ~f:(fun (fn, eqn) -> (fn, pick_one_join fn eqn))
         (im_to_fields sinfo sinfo.func_info.eqns))
  in
  pf fout "@[<v 2>(define (%s %s %s)@;@[%a@])@]@." sinfo.join_name sinfo.func_info.lstate.vname
    sinfo.func_info.rstate.vname rpp_term join_body

(* ==============================================================================================*)
(* =========================    Specification and variables     =================================*)

let pp_struct_equality_name fout select_fields sinfo =
  let struct_name, struct_fields = VarSet.to_struct sinfo.func_info.vars in
  let relevant_struct_fields =
    match select_fields with
    | Some field_names ->
        List.filter ~f:(fun (s, _) -> List.mem field_names ~equal:String.equal s) struct_fields
    | None -> struct_fields
  in
  let struct_equality_name = Naming.struct_equality_name struct_name in
  let s1_name = "s1" in
  let s2_name = "s2" in
  pf fout "@[<v 2>(define (%s %s %s)@;@[< v 2>(and@;%a)@])@]@." struct_equality_name s1_name s2_name
    (list ~sep:sp (fun f (fname, _) ->
         pf f "(equal? (%s-%s %s) (%s-%s %s))" struct_name fname s1_name struct_name fname s2_name))
    relevant_struct_fields;
  struct_equality_name

let pp_input_assumptions fout sinfo unq_symb_inputs =
  (* Print user-defined assertions. *)
  match sinfo.func_info.assume_input with
  | Some assertion ->
      let ox = VarSet.max_elt (Lang.Analyze.free_variables assertion) in
      let f sd =
        let elts =
          match sd.s_term.texpr with
          | EList l -> (
              match ox with
              | Some x ->
                  List.map l ~f:(fun y ->
                      Lang.Unfold.reduce_exn (replace_expr ~old:(mk_vt x) ~by:y assertion))
              | None -> List.map l ~f:(fun _ -> assertion) )
          | _ -> []
        in
        pf fout "@[<hov 2>(assert (and %a))@]@.@." (list ~sep:sp (box rpp_term)) elts
      in
      f unq_symb_inputs
  | None -> ()

let pp_assertion_join symb_inputs sname frmt sinfo =
  match symb_inputs with
  | [ (_, sd) ] ->
      List.iter (infer_divisions sinfo) ~f:(fun i ->
          Fmt.(
            pf frmt "@[(%s (%s (%s (take %s %i)) (%s (drop %s %i))) (%s %s))@]@;" sname
              sinfo.join_name sinfo.func_name sd.s_variable.vname i sinfo.func_name
              sd.s_variable.vname i sinfo.func_name sd.s_variable.vname))
  | _ -> failwith "Multiple input lists not supported."

let pp_synthesize_objective select_fields (sinfo : eqs_soln_info) (fout : Formatter.t) =
  let symb_inputs =
    List.map
      ~f:(fun v -> (v, mk_symb_term ~len:!Utils.Config.sl_join_synt_len v.vtype))
      (Set.to_list sinfo.func_info.collection_inputs)
  in
  let uq_vars =
    List.fold
      ~f:(fun accum (_, sd) -> accum $|| Rosette.pp_symbolic_define fout sd)
      ~init:VarSet.empty symb_inputs
  in
  List.iter ~f:(fun sd -> pp_input_assumptions fout sinfo sd) (ListTools.lsnd symb_inputs);
  (* Print the equality definition. *)
  let struct_equality_name = pp_struct_equality_name fout select_fields sinfo in
  (* Print the (synthesize ..) construct. *)
  let objective = "$$_obj" in
  pp_separator_line fout ();
  pf fout
    "(define %s\n\
    \      (synthesize\n\
    \        #:forall (list %a)\n\
    \        #:guarantee (assert @[<v 2>(and@;\
     %a)@])))@."
    objective
    (list ~sep:(Fmt.any " ") pp_variable)
    (Set.to_list uq_vars)
    (pp_assertion_join symb_inputs struct_equality_name)
    sinfo;
  pp_newline fout ();
  pp_output_sketch_to_file ~file_out:sinfo.tmp_file_out ~obj:objective fout ();
  pf fout ";; sketching level : % i.@." sinfo.sketching_level

let compile_sketch ?(select_fields = None) si =
  Log.debug ~level:1
    Fmt.(fun f () -> pf f "Sketch compiling in %s (output %s)" si.tmp_file_sk si.tmp_file_out);
  let oc = OC.create si.tmp_file_sk in
  let fout = Stdlib.Format.formatter_of_out_channel oc in
  Fmt.set_utf_8 fout false;
  Stdlib.Format.pp_set_margin fout 100;
  pp_lang_def_rosette fout ();
  pp_newline fout ();
  pp_struct_defs si fout;
  pp_input_defs si fout;
  pp_separator_line fout ();
  pp_orig_func_def si fout;
  pp_separator_line fout ();
  pp_join select_fields si fout;
  pp_separator_line fout ();
  pp_synthesize_objective select_fields si fout;
  OC.close oc
