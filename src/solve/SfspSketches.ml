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

let _otimes_func_name = "_$otimes"

let _pre_func_name = "_$pre"

let _post_func_name = "_$post"

let _pred_name = "_$pred"

let _divide_name = "_$divide"

let _join_name = "_$join"

let pp_struct_defs (si : std_soln) (frmt : Formatter.t) =
  let used_structs =
    Lang.Analyze.used_structs
      (mk_list [ si.sf_init; si.sf_pre.body; si.sf_post.body; si.sf_otimes.body ])
  in
  pre_pp_struct_defs frmt used_structs

let pp_input_defs (_ : std_soln) (_ : Formatter.t) = ()

(* ==============================================================================================*)
(* ========================= Self-Fold Single Pass Function  ====================================*)

let pp_sfsp_pre (si : std_soln) (fout : Formatter.t) =
  pf fout "#| sfsp_%s : @[%a -> %a -> %a@] |#@." _pre_func_name pp_typ_short si.sf_pre.s.vtype
    pp_typ_short si.sf_pre.a.vtype pp_typ_short (type_of_exn si.sf_pre.body);
  pf fout "@[<v 2>(define (%s %s %s)@;%a)@]@." _pre_func_name si.sf_pre.s.vname si.sf_pre.a.vname
    (box rpp_term) si.sf_pre.body

let pp_sfsp_post (si : std_soln) (fout : Formatter.t) =
  pf fout "#| %s : @[%a -> %a -> %a@] |#@." _post_func_name pp_typ_short si.sf_post.s.vtype
    pp_typ_short si.sf_post.a.vtype pp_typ_short (type_of_exn si.sf_post.body);
  pf fout "@[<v 2>(define (%s %s %s)@;%a)@]@." _post_func_name si.sf_post.s.vname si.sf_post.a.vname
    (box rpp_term) si.sf_post.body

let pp_sfsp_otimes (si : std_soln) (fout : Formatter.t) =
  pf fout "#| %s : @[%a -> %a -> %a -> %a@] |#@." _otimes_func_name pp_typ_short
    si.sf_otimes.a.vtype pp_typ_short si.sf_otimes.s.vtype pp_typ_short si.sf_otimes.e.vtype
    pp_typ_short (type_of_exn si.sf_otimes.body);
  pf fout "@[<v 2>(define (%s %s %s %s)@;%a)@]@." _otimes_func_name si.sf_otimes.a.vname
    si.sf_otimes.s.vname si.sf_otimes.e.vname (box rpp_term) si.sf_otimes.body

let pp_sfsp_common (fout : Formatter.t) (si : std_soln) () =
  let pp_sfsp_init_sketch frmt () = rpp_term frmt si.sf_init in
  match si.sf_ret with
  | TStruct (sn, _) ->
      pf fout
        "@[<hov 2>(define (sfsp_oplus s a)@;\
         (%s (foldl (lambda (e s) (%s a s e)) (%s s a) (%s-%s s)) a))@." _post_func_name
        _otimes_func_name _pre_func_name sn si.sf_li;
      pf fout "@[<hov 2>(define (%s %s)@;(foldl (lambda (a s) (sfsp_oplus s a)) @[%a@] %s))@]@."
        si.sf_func.vname (fst si.sf_input).vname (box pp_sfsp_init_sketch) ()
        (fst si.sf_input).vname
  | _ -> failwith "Unexpected form of std_soln"

let pp_assertions_on_inputs fout si (unq_vars, unq_symb_inputs) =
  (* Print user-defined assertions. *)
  ( match snd si.sf_input with
  | Some assertion ->
      let ox = VarSet.max_elt (Lang.Analyze.free_variables assertion) in
      let f sd =
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
        pf fout "@[<hov 2>(assert (and %a))@]@.@." (list ~sep:sp (box rpp_term)) elts
      in
      f unq_symb_inputs
  | None -> () );
  (* Assert integers are in the considered range. *)
  let int_symbs = List.filter ~f:(fun v -> ETypes.(v.vtype = TInt)) (Set.elements unq_vars) in
  let pp_range_assertion formt v =
    pf formt "(and (< (- %i) %s) (> %i %s))" int_range v.vname int_range v.vname
  in
  pf fout "@[<hov 2>(assert (and %a))@]@.@." (list ~sep:sp (box pp_range_assertion)) int_symbs
