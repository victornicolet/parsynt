open Base
open Fmt
open Predefs
open Lang
open Lang.Term
open Lang.TermUtils
open Lang.Typ
open Lang.SolutionDescriptors
open Utils
open TermPp
module OC = Stdio.Out_channel

let otimes_func_name = "_$otimes"

let pre_func_name = "_$pre"

let post_func_name = "_$post"

let pp_input_defs (vs : VarSet.t) (fout : Formatter.t) =
  let symb_inputs =
    List.map
      ~f:(fun v -> (v, mk_symb_term ~name_hint:v.vname ~len:!Utils.Config.sfsp_synt_len v.vtype))
      (Set.elements vs)
  in
  let uq_vars =
    List.fold
      ~f:(fun accum (v, sd) ->
        accum
        $|| Rosette.pp_symbolic_define ~force_name:(Some v.vname) fout { sd with s_variable = v })
      ~init:VarSet.empty symb_inputs
  in
  uq_vars

let pp_struct_defs (si : soln_info) (frmt : Formatter.t) =
  let used_structs =
    Lang.Analyze.used_structs
      (mk_list [ si.func_body; si.init; si.pre.body; si.post.body; si.otimes.body ])
  in
  pre_pp_struct_defs frmt used_structs

let pp_sfsp_pre (si : soln_info) (fout : Formatter.t) =
  (* Debugging aid : print the type of the function *)
  pf fout "#| sfsp_%s : @[%a -> %a -> %a@] |#@." pre_func_name pp_typ_short si.pre.s.vtype
    pp_typ_short si.pre.a.vtype pp_typ_short (type_of_exn si.pre.body);
  (* The actual sketch of the term *)
  pf fout "@[<v 2>(define (%s %s %s)@;%a)@]@." pre_func_name si.pre.s.vname si.pre.a.vname
    (box rpp_term) si.pre.body

let pp_sfsp_post (si : soln_info) (fout : Formatter.t) =
  (* Debugging aid : print the type of the function *)
  pf fout "#| %s : @[%a -> %a -> %a@] |#@." post_func_name pp_typ_short si.post.s.vtype pp_typ_short
    si.post.a.vtype pp_typ_short (type_of_exn si.post.body);
  (* The actual sketch of the term *)
  pf fout "@[<v 2>(define (%s %s %s)@;%a)@]@." post_func_name si.post.s.vname si.post.a.vname
    (box rpp_term) si.post.body

let pp_sfsp_otimes (si : soln_info) (fout : Formatter.t) =
  (* Debugging aid : print the type of the function *)
  pf fout "#| %s : @[%a -> %a -> %a -> %a@] |#@." otimes_func_name pp_typ_short si.otimes.a.vtype
    pp_typ_short si.otimes.s.vtype pp_typ_short si.otimes.e.vtype pp_typ_short
    (type_of_exn si.otimes.body);
  (* The actual sketch of the term *)
  pf fout "@[<v 2>(define (%s %s %s %s)@;%a)@]@." otimes_func_name si.otimes.a.vname
    si.otimes.s.vname si.otimes.e.vname (box rpp_term) si.otimes.body

let pp_sfsp_common (fout : Formatter.t) (si : soln_info) () =
  let pp_sfsp_init_sketch frmt () = rpp_term frmt si.init in
  match (si.target_accum_type, si.list_field_name) with
  | TStruct (sn, _), Some lfn ->
      pf fout
        "@[<hov 2>(define (sfsp_oplus s a)@;\
         (%s (foldl (lambda (e s) (%s a s e)) (%s s a) (%s-%s s)) a))@." post_func_name
        otimes_func_name pre_func_name sn lfn;
      pf fout "@[<hov 2>(define (%s %s)@;(foldl (lambda (a s) (sfsp_oplus s a)) @[%a@] %s))@]@."
        si.target_func_name si.func_input.vname (box pp_sfsp_init_sketch) () si.func_input.vname
  | TList _, None ->
      pf fout
        "(define (sfsp_oplus s a)\n        (%s (foldl (lambda (e s) (%s a s e)) (%s s a) s) a))@."
        post_func_name otimes_func_name pre_func_name;
      pf fout "(define (%s %s)\n        (foldl (lambda (a s) (sfsp_oplus s a)) %a %s))@."
        si.target_func_name si.func_input.vname (box pp_sfsp_init_sketch) () si.func_input.vname
  | _, _ -> failwith "Wrong input types for sketch."

let pp_orig_func_def (si : soln_info) (fout : Formatter.t) =
  pf fout "@[(define (%s %a) %a)@.@]" si.func_name string si.func_input.vname rpp_term si.func_body

let pp_synthesize_objective extra_uq (sinfo : soln_info) (fout : Formatter.t) =
  let sfsp_out = type_term_exn sinfo.post.body in
  let projection =
    if ETypes.(sfsp_out.ttyp = sinfo.return_type) then []
    else
      match (sinfo.return_type, sfsp_out.ttyp) with
      (* Input struct has been lifted, project new on original. *)
      | TStruct (s1, mems1), TStruct (s2, mems2) ->
          List.filter_map mems1 ~f:(fun (fname, _) ->
              match List.Assoc.find ~equal:String.equal mems2 fname with
              | Some _ -> Some (Some s1, fname, s2)
              | _ -> None)
      (* Input simple type has been lifted, project new struct. *)
      | (TBool | TInt | TList _), TStruct (s2, mems2) ->
          List.filter_map mems2 ~f:(fun (fname, ftype) ->
              if ETypes.(ftype = sinfo.return_type) then Some (None, fname, s2) else None)
      | _ -> []
  in

  ( match projection with
  | [] -> pf fout "(define equal-$? equal?)"
  | l ->
      pf fout "@[<v 2>(define (equal-$? s1 s2)@;(and@;@[%a@]))@]@."
        (list ~sep:sp (fun f (s1, fname, s2) ->
             match s1 with
             | Some s1 -> pf f "(equal? (%s-%s s1) (%s-%s s2))" s1 fname s2 fname
             | None -> pf f "(equal? s1 (%s-%s s2))" s2 fname))
        l );
  let symb_inputs =
    List.map
      ~f:(fun v -> (v, mk_symb_term ~len:!Utils.Config.sfsp_synt_len v.vtype))
      [ sinfo.func_input ]
  in
  let uq_vars =
    List.fold
      ~f:(fun accum (_, sd) -> accum $|| Rosette.pp_symbolic_define fout sd)
      ~init:VarSet.empty symb_inputs
  in
  let pp_assertions fout () =
    match sinfo.func_input_assert with
    | Some assertion ->
        let ox = VarSet.max_elt (Lang.Analyze.free_variables assertion) in
        let f (_, sd) =
          let elts =
            match sd.s_term.texpr with
            | EList l -> (
                match ox with
                | Some x ->
                    List.map l ~f:(fun y ->
                        Unfold.reduce_exn (replace_expr ~old:(mk_vt x) ~by:y assertion))
                | None -> List.map l ~f:(fun _ -> assertion) )
            | _ -> []
          in
          pf fout "@[<hov 2>(assert (and %a))@]@." (list ~sep:sp (box rpp_term)) elts
        in
        List.iter ~f symb_inputs
    | None -> ()
  in
  let pp_assertion_sfsp frmt sinfo =
    match symb_inputs with
    | [ (_, sd) ] ->
        Fmt.(
          pf frmt "(%s (%s %s) (%s %s))"
            ( if sinfo.return_type_as_set && is_list sinfo.return_type then "equal-sets?"
            else "equal-$?" )
            sinfo.func_name sd.s_variable.vname sinfo.target_func_name sd.s_variable.vname)
    | _ -> failwith "Multiple input lists not supported."
  in
  let objective = "$$_obj" in
  pp_separator_line fout ();
  pp_assertions fout ();
  pp_separator_line fout ();

  (* begin
     match symb_inputs with
     | [_, sd] ->
      pf fout
        "(%s %s)@.(%s %s)@.@."
        sinfo.func_name sd.s_variable.vname
        sinfo.target_func_name sd.s_variable.vname
     | _ -> ()
     end; *)
  pf fout
    "(define %s\n      (synthesize\n        #:forall (list %a)\n        #:guarantee (assert %a)))@."
    objective
    (list ~sep:(Fmt.any " ") pp_variable)
    (Set.to_list (uq_vars $|| extra_uq))
    pp_assertion_sfsp sinfo;
  pf fout "@.(define output-file (open-output-file \"%s\" #:exists 'truncate))@." sinfo.tmp_file_out;
  pf fout
    "(if (sat? %s)\n\
    \      (begin\n\
    \        (define form_list  (generate-forms %s))\n\
    \        (if (empty? form_list)\n\
    \          (println \"sat\" output-file)\n\
    \          (map\n\
    \            (lambda (forms)\n\
    \              (println (syntax->datum forms) output-file))\n\
    \              form_list)))\n\
    \      (println \"unsat\" output-file))\n\
    \   (close-output-port output-file)\n\
    \   (exit)" objective objective

let compile_sfsp_sketch (si : soln_info) =
  let unbound = Set.remove (Analyze.free_variables si.func_body) si.func_input in
  if !Log.verbose then Log.debug (string_msg "Sketch compiling in %s" si.tmp_file_sk);
  let oc = OC.create si.tmp_file_sk in
  let fout = Stdlib.Format.formatter_of_out_channel oc in
  Fmt.set_utf_8 fout false;
  Stdlib.Format.pp_set_margin fout 100;
  pp_lang_def_rosette fout ();
  pp_newline fout ();
  if si.return_type_as_set then pp_list_as_set_equality fout () else ();
  pp_struct_defs si fout;
  let extra_uq = pp_input_defs unbound fout in
  pp_separator_line fout ();
  pp_sfsp_pre si fout;
  pp_newline fout ();
  pp_sfsp_post si fout;
  pp_newline fout ();
  pp_sfsp_otimes si fout;
  pp_newline fout ();
  pp_sfsp_common fout si ();
  pp_separator_line fout ();
  pp_orig_func_def si fout;
  pp_separator_line fout ();
  pp_synthesize_objective extra_uq si fout;
  OC.close oc
