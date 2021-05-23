open Base
open Fmt
open Predefs
open Lang
open Lang.Term
open Lang.Typ
open Lang.ResourceModel
open Lang.SolutionDescriptors
open SfspSketches
open TermPp
open Utils
module OC = Stdio.Out_channel

let divide_len = ref 4

(* ==============================================================================================*)
(* =========================    Predicate and divide sketch     =================================*)

let pp_predicate (fout : Formatter.t) (pi : pred_soln) () =
  pf fout "(define @[(%s %a)@] %a)@." _pred_name (list ~sep:sp pp_variable) (fst pi.predicate)
    (box rpp_term) (snd pi.predicate)

let pp_div (fout : Formatter.t) (pi : pred_soln) () =
  let aux (divide : div_soln) =
    let partitions =
      let pp_def (fv, body) =
        pf fout "(define @[(%s %a)@] %a)@.@." fv.vname (list ~sep:sp pp_variable)
          (get_pivots divide) (box rpp_term) body;
        fv.vname
      in
      List.map ~f:pp_def divide.partitions
    in
    let pivots_after_print =
      let f l (pivot_v, (pivot_f, piv_args), pivot_body) =
        let fname = pivot_f.vname in
        let fargs = divide.x :: piv_args in
        pf fout "@[(define (%s %a) %a)@]@.@." fname (list ~sep:sp pp_variable) fargs (box rpp_term)
          pivot_body;
        l @ [ (pivot_v.vname, fname, fargs) ]
      in
      List.fold ~f ~init:[] divide.pivots
    in
    let pp_partitions fmt () =
      let rec pp_parts i xis parts fmt () =
        match parts with
        | hd :: tl ->
            let x, xis' = (List.last_exn xis, List.drop_last_exn xis) in
            let xi, xi1 = (x ^ Int.to_string i, x ^ Int.to_string (i + 1)) in
            pf fmt "@[(let-values ([(%s %s) (partition (%s %a) %s)]) %a)@]" xi xi1 hd
              (list ~sep:sp pp_variable) (get_pivots divide) x (* Input list *)
              (pp_parts (i + 2) (xis' @ [ xi; xi1 ]) tl)
              ()
        | _ -> pf fmt "@[(values %a)@]" (list ~sep:sp string) xis
      in
      pp_parts 1 [ divide.x.vname ] partitions fmt ()
    in
    let rec pp_pivots fmt pivot_sels =
      match pivot_sels with
      | [] -> pp_partitions fmt ()
      | (pivot, pivot_selec, args) :: tl ->
          pf fmt "(let@;@[([%s (%s %a)])@]@;%a)" pivot pivot_selec (list ~sep:sp pp_variable) args
            pp_pivots tl
    in
    pf fout "@[<hov 2>@[(define (%s %s)@]@;%a)@]@." _divide_name divide.x.vname pp_pivots
      pivots_after_print
  in
  match pi.divide with Some divide -> aux divide | None -> ()

(* ==============================================================================================*)
(* =========================    Specification and variables     =================================*)

let pp_synthesize_objective (fout : Formatter.t) (pi : pred_soln) : unit =
  let si = pi.base in
  let unq_symb_inputs = mk_symb_term ~len:!divide_len (fst si.sf_input).vtype in
  let unq_vars = Rosette.pp_symbolic_define fout unq_symb_inputs in
  let n = !divide_len in
  let unq_divs =
    List.map ~f:(fun _ -> mk_var ~name:"$X" (fst si.sf_input).vtype) (List.range 0 pi.budget.c)
  and existq_divs =
    let f i =
      ( i,
        List.map ~f:(fun _ -> mk_var ~name:"$L" (fst si.sf_input).vtype) (List.range 0 pi.budget.c),
        let symbs = mk_symb_term ~len:!divide_len (fst si.sf_input).vtype in
        let _ = Rosette.pp_symbolic_define fout symbs in
        symbs )
    in
    List.map ~f (List.range 1 (n - 1))
  in
  let pp_chi fmt () =
    let f (j, vars, _) =
      match vars with
      | [ l1; l2; l3 ] ->
          pf fmt "(= (length %s) %i)@;(= (length %s) %i)@;(= (length %s) %i)" l1.vname j l2.vname
            ((n - j) / 2)
            l3.vname
            ((n - j + 1) / 2)
      | [ l1; l2 ] -> pf fmt "(= (length %s) %i)@;(= (length %s) %i)@;" l1.vname j l2.vname (n - j)
      | [ l1 ] -> pf fmt "(= (length %s) %i)" l1.vname n
      | _ -> pf fmt ""
    in
    List.iter ~f existq_divs
  in
  let pp_assertion fmt () =
    pf fmt "@[<hov 2>(and (%s %a) %a)@]" (* Psi - divide constraint *) _pred_name
      (list ~sep:sp pp_variable) unq_divs (* chi - divide quality. *) pp_chi ()
  in
  let objective = Alpha.get_new_name "$$_obj" in
  let _ =
    match (fst si.sf_input).vtype with
    | TList (TStruct (struct_name, fields)) ->
        let struct_equality_name = Naming.struct_equality_name struct_name in
        let s1_name = "s1" in
        let s2_name = "s2" in
        pf fout "@[<v 2>(define (%s %s %s)@;@[< v 2>(and@;%a)@])@]@.@." struct_equality_name s1_name
          s2_name
          (list ~sep:sp (fun f (fname, ftype) ->
               match ftype with
               | TList _ when si.sf_as_set ->
                   pf f "(equal-sets? (%s-%s %s) (%s-%s %s))" struct_name fname s1_name struct_name
                     fname s2_name
               | _ ->
                   pf f "(equal? (%s-%s %s) (%s-%s %s))" struct_name fname s1_name struct_name fname
                     s2_name))
          fields;
        struct_equality_name
    | TList (TBool | TInt) -> "="
    | _ -> "+"
  in
  let pp_assertions fout () =
    let exq_symb_defs = ListTools.lthird existq_divs in
    let all_symb_defs = unq_symb_inputs :: exq_symb_defs in
    match snd si.sf_input with
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
          pf fout "@[<hov 2>(assert (and %a))@]@." (list ~sep:sp (box rpp_term)) elts
        in
        List.iter ~f all_symb_defs
    | None -> ()
  in
  List.iter existq_divs ~f:(fun (_, _, sd) ->
      pf fout
        "@[(for ((x (combinations (list %a) 2))) (assert (not (equal? (car x) (cadr x)))))@]@."
        (list ~sep:sp pp_variable) (Set.elements sd.s_vars));

  pp_newline fout ();
  pf fout "@[(define-values (%a) (%s %s))@]@." (list ~sep:sp pp_variable) unq_divs _divide_name
    unq_symb_inputs.s_variable.vname;
  pp_newline fout ();
  List.iter existq_divs ~f:(fun (_, exq_divs, exq_symb_inputs) ->
      pf fout "@[(define-values (%a) (%s %s))@]@." (list ~sep:sp pp_variable) exq_divs _divide_name
        exq_symb_inputs.s_variable.vname);
  pp_newline fout ();
  pp_separator_line fout ();
  pp_assertions fout ();
  pf fout
    "(define %s\n\
    \      (synthesize\n\
    \        #:forall (list %a)\n\
    \        #:guarantee @[<hov 2>(assert %a)@]))@." objective
    (box (list ~sep:(Fmt.any " ") pp_variable))
    (Set.to_list unq_vars) (box pp_assertion) ();
  pp_output_sketch_to_file ~file_out:pi.tmp_file_out ~obj:objective fout ()

let compile_divide_sketch (pi : pred_soln) : unit =
  if Option.is_none pi.divide then ()
  else
    let si = pi.base in
    if !Log.verbose then
      Log.info_msg (Fmt.str "Sketch compiling in %s (output in %s)." pi.tmp_file_sk pi.tmp_file_out);
    let oc = OC.create pi.tmp_file_sk in
    let fout = Stdlib.Format.formatter_of_out_channel oc in
    Fmt.set_utf_8 fout false;
    Stdlib.Format.pp_set_margin fout 100;
    pp_lang_def_rosette fout ();
    pp_newline fout ();
    if si.sf_as_set then pp_list_as_set_equality fout () else ();
    pp_struct_defs si fout;
    pp_input_defs si fout;
    pp_separator_line fout ();
    pp_sfsp_pre si fout;
    pp_newline fout ();
    pp_sfsp_post si fout;
    pp_newline fout ();
    pp_sfsp_otimes si fout;
    pp_newline fout ();
    pp_sfsp_common fout si ();
    pp_separator_line fout ();
    pp_predicate fout pi ();
    pp_newline fout ();
    pp_div fout pi ();
    pp_separator_line fout ();
    pp_synthesize_objective fout pi;
    OC.close oc
