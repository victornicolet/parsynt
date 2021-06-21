open Base
open Lang.Normalize
open Lang.Term
open Lang.Typ
open Lang.TermPp
open Lang.TermUtils
open Lang.ResourceModel
open Solve.STerm
open Solve.Scripting
open Solve.SolverForms
open Recursion.SymbExe
open Utils
module Smt = Solve.SolverForms

let normalize_command (do_mcnf : bool) (ce : resource list) (e : term) =
  if do_mcnf then (
    let mcnf = to_mcnf e in
    let solver = make_z3_solver () in
    let _, decls, _ = build_terms (terms_of_resources ce) in
    let _, decls', _ = build_smt_term e in
    declare_all solver (decls @ decls');
    List.map
      ~f:(fun (cond, e') ->
        (* Simplify conditions. *)
        let conj = mk_conj cond in
        ( (match Smt.z3_simplify ~solver:(Some solver) conj with Some c -> c | None -> conj),
          (* Normalize expressions. *)
          normalize ~costly:ce e' ))
      (compress_mcnf ~solver mcnf) )
  else [ (mk_true, normalize ~costly:ce e) ]

let pp_command (formt : Formatter.t) (command : external_command) =
  match command with
  | CCEval (env, e) ->
      let solver = make_z3_solver () in
      let _, decls, _ = build_terms (List.map ~f:snd (Map.to_alist env.evals)) in
      declare_all solver decls;
      let t = branching_eval solver env e in
      Fmt.(pf formt "%a@." (box pp_term) t);
      Fmt.(pf formt "MCNF:@.%a." pp_mcnf (compress_mcnf ~solver (to_mcnf t)))
  | CNormalize (do_mcnf, ce, e) ->
      let command_res = normalize_command do_mcnf (resources_of_terms ce) e in
      List.iter
        ~f:(fun (cond, e') -> Fmt.(pf formt "{%a when %a}@." pp_term e' (box pp_term) cond))
        command_res
  | CCollect (do_mcnf, ce, e) ->
      let command_res =
        if do_mcnf then
          let _ = to_mcnf e in
          [] (* collect_mcnf ~costly:ce (normalize_branches_mcnf ~costly:ce (compress_mcnf mcnf)) *)
        else
          let re = resources_of_terms ce in
          Recursion.Collect._costly := re;
          [ ([], Recursion.Collect.collect (normalize ~costly:re e)) ]
      in
      Fmt.(
        (box (list ~sep:cut Recursion.Collect.pp_collect_result))
          formt (List.map ~f:snd command_res))
  | CAnnotateUnfoldings (ce, e1, e2) ->
      let c1 = normalize_command true (resources_of_terms ce) e1 in
      let c2 = normalize_command true (resources_of_terms ce) e2 in
      let impls =
        List.map
          ~f:(fun (ec1, ec2) -> mk_not (mk_and ec2 ec1))
          (List.cartesian_product (List.map ~f:fst c1) (List.map ~f:fst c2))
      in
      let cs e = (e, Smt.check_simple e) in
      List.iter
        ~f:(fun (e, sat) ->
          Fmt.(pf formt "[%a => %a]@." (box pp_term) e (box Smt.pp_solver_response) sat))
        (List.map ~f:cs impls)
  | CDiscover _ -> failwith "Deprecated."
  (* let res = discover ~name:fname ~conc_init:s0 ~f:f_expr in
     Fmt.(pf stdout "@.@.          ========== SUMMARY ==========@.");
     Fmt.((box (result ~ok:pp_res_discover ~error:Sexp.pp) formt res)) *)
  | CPrint s -> Fmt.(pf formt "%a@." string s)
