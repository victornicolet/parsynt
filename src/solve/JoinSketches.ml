open Base
open Fmt
open Predefs
open Lang
open Lang.Term
open Lang.Typ
open Lang.ResourceModel
open Lang.SolutionDescriptors
open TermPp
open SfspSketches
open Utils
module OC = Stdio.Out_channel

let join_len = ref 4

(* ==============================================================================================*)
(* =========================     Divide and join sketch     =================================*)
let split_div (n : int) =
  if n = 2 then
    let k = !join_len / 2 in
    Fmt.str "(values (take X %i) (drop X %i))" k k
  else if n = 3 then
    let k = !join_len / 3 in
    Fmt.str "(let ([l1 (take X %i)] [l2 (drop X %i)]) (values l1 (take l2 %i) (drop l2 %i))" k k k k
  else failwith "Splitting divide for n > 3 not supported."

let pp_div (fout : Formatter.t) (ji : join_soln) () =
  match ji.divide with
  | Some divide_func ->
      let div_term = term_of_div_soln divide_func in
      pf fout "@[<hov 2>@[(define (%s %s)@]@;%a)@]@." _divide_name divide_func.x.vname rpp_term
        div_term
      (* The divide is a splitting divide. *)
  | None -> pf fout "@[<hov 2>@[(define (%s X)@]@;%s)@]@." _divide_name (split_div ji.budget.c)

let pp_join (fout : Formatter.t) (ji : join_soln) () =
  let join_vars, join_body = ji.join in
  pf fout "@[<hov 2>@[(define (%s %a)@]@;%a)@]@." _join_name (list ~sep:sp pp_variable) join_vars
    (box rpp_term) join_body

(* ==============================================================================================*)
(* =========================    Specification and variables     =================================*)

let pp_synthesize_objective (fout : Formatter.t) (ji : join_soln) : unit =
  let si = ji.base in
  let unq_symb_inputs = mk_symb_term ~len:!join_len (fst si.sf_input).vtype in
  let unq_vars = Rosette.pp_symbolic_define fout unq_symb_inputs in
  let unq_divs =
    List.map ~f:(fun _ -> mk_var ~name:"$X" (fst si.sf_input).vtype) (List.range 0 ji.budget.c)
  in
  let objective = Alpha.get_new_name "$$_obj" in
  let eq_name =
    match si.sf_ret with
    | TStruct (struct_name, fields) ->
        let struct_equality_name = Naming.struct_equality_name struct_name in
        let s1_name = "s1" in
        let s2_name = "s2" in
        pf fout "@[<v 2>(define (%s %s %s)@;@[< v 2>(and@;%a)@])@]@." struct_equality_name s1_name
          s2_name
          (list ~sep:sp (fun f (fname, ftype) ->
               match ftype with
               | TList _ when si.sf_as_set ->
                   pf f "(equal-sets? (%s-%s %s) (%s-%s %s))" struct_name fname s1_name struct_name
                     fname s2_name
               | _ ->
                   pf f "(eq? (%s-%s %s) (%s-%s %s))" struct_name fname s1_name struct_name fname
                     s2_name))
          fields;
        struct_equality_name
    | TList (TBool | TInt) -> "="
    | _ -> "+"
  in
  let pp_assertion fmt () =
    pf fmt "(if (or %a) #t (%s (%s %a) (%s %s)))"
      (list ~sep:sp (fun fmt l -> pf fmt "(empty? %s)" l.vname))
      unq_divs eq_name _join_name
      (list ~sep:sp (fun fmt l -> pf fmt "(%s %s)" si.sf_func.vname l.vname))
      (List.take unq_divs ji.budget.m) si.sf_func.vname unq_symb_inputs.s_variable.vname
    (* pf fmt "(%s (%s %a) (%s %s))" eq_name _join_name
       (list ~sep:sp (fun fmt l -> pf fmt "(%s %s)" si.sf_func.vname l.vname))
       (List.take unq_divs ji.budget.m) si.sf_func.vname unq_symb_inputs.s_variable.vname *)
  in
  pp_newline fout ();
  pf fout "@[(define-values (%a) (%s %s))@]@." (list ~sep:sp pp_variable) unq_divs _divide_name
    unq_symb_inputs.s_variable.vname;
  pp_newline fout ();
  pp_assertions_on_inputs fout si (unq_vars, unq_symb_inputs);
  pp_newline fout ();
  pf fout "(define %s\n  (synthesize\n    #:forall (list %a)\n    #:guarantee (assert %a)))@."
    objective
    (box (list ~sep:(Fmt.any " ") pp_variable))
    (Set.to_list unq_vars) (box pp_assertion) ();
  pp_output_sketch_to_file ~file_out:ji.tmp_file_out ~obj:objective fout ()

let compile_join_sketch (ji : join_soln) : unit =
  let si = ji.base in
  Log.info_msg Fmt.(str "Sketch compiling in %s (output in %s)" ji.tmp_file_sk ji.tmp_file_out);
  let oc = OC.create ji.tmp_file_sk in
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
  pp_div fout ji ();
  pp_separator_line fout ();
  pp_join fout ji ();
  pp_separator_line fout ();
  pp_synthesize_objective fout ji;
  OC.close oc
