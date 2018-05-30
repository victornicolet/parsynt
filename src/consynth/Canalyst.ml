(**
   This file is part of Parsynt.

    Foobar is free software: you can redistribute it and/or modify
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

open Beta
open Sketch
open Format
open Utils
open Utils.PpTools
open FError
open FuncTypes
open SymbExe
open VariableDiscovery
open Loops
open Conf

module E = Errormsg
module C = Cil
(* module Cl = Cloop *)
module A = AnalyzeLoops
(* module Z3E = Z3engine *)

let debug = ref false
let verbose = ref false
(* Do not remove dead code, some of this
   dead code is useful in the examples *)
let elimDeadCode = ref false


let parseOneFile (fname : string) : C.file =
  try
    Frontc.parse fname ()
  with
    Errormsg.Error ->
    failhere __FILE__ "parseOneFile" "Error while parsing input file,\
              the filename might contain errors"



let processFile fileName =
  C.initCIL ();
  C.insertImplicitCasts := false;
  C.lineLength := 1000;
  C.warnTruncate := false;
  Cabs2cil.doCollapseCallCast := true;
  (* Some declarations are found in another file,
     like __max_integer__, true, false, ... *)
  let decl_header =
    parseOneFile (Conf.template "decl_header.h")
  in
  let cfile = Mergecil.merge [decl_header; parseOneFile fileName] "main" in
  Cfg.computeFileCFG cfile;
  if !elimDeadCode then  Deadcodeelim.dce cfile;
  Loops.debug := !debug;
  Loops.verbose := !verbose;
  process_file cfile;
  let loops = get_loops () in
  if !verbose then
    begin
      printf "Input loops@.";
      IH.iter
        (fun lid cl -> CilTools.pps cl.lstmt) loops;
    end;
  cfile,
  IH.fold
    (fun k cl m ->
       register_vs cl.lvariables.all_vars;
       IM.add k cl m)
    loops
    IM.empty

(**
   Returns a tuple with :
   - list of variables ids that a read in the loop.
   - list of state variables (written)
   - the set of variables defined in the loop.
   - a triplet for the init, guard and update of the index of the loop.
   - the function representing the body of the loop.
   - a mapping from variables to constants for variables
   that have a static initialization before the loop.
*)
type figu = VS.t * (Cil2Func.letin * Cil2Func.expr * Cil2Func.letin)
type varset_info = int list * int list * VS.t
type func_info =
  {
    host_function : Cil.varinfo;
    mutable func : Cil2Func.letin;
    mutable figu : figu option;
    lid : int;
    loop_name : string;
    lvariables : variables;
    mutable reaching_consts : Cil.exp Utils.IM.t;
    mutable inner_funcs : func_info list;
  }

let rec init_func_info linfo =
  {
    host_function = linfo.lcontext.host_function;
    func = Cil2Func.empty_state ();
    figu = None;
    lid = linfo.lid;
    loop_name = Conf.inner_loop_func_name linfo.lcontext.host_function.Cil.vname
        linfo.lid;
    lvariables = linfo.lvariables;
    reaching_consts = IM.empty;
    inner_funcs = List.map init_func_info linfo.inner_loops;
  }
(**
   Sketch info type :
    - subset of read variables
    - subset of written variables,
    - set of variables in the function
    - body of the function
    - init, guard and update of the enclosing loop
    - sketch of the join.
*)
type sigu = VS.t * (fnExpr * fnExpr * fnExpr)

(**
   From cil loop bodies to intermediary function representation.
   This step only translates the control-flow of the input C program,
   the expressions will be translated later.
*)
let cil2func cfile loops =
  Cil2Func.init loops;

  let sorted_lps = A.transform_and_sort loops in

  let rec translate_loop loop =
    let finfo = init_func_info loop in

    if !verbose then
      (printf "@.%s=== Loop %i in %s ===%s"
         (color "blue") loop.lid loop.lcontext.host_function.C.vname color_default;
       printf "@.Identified state variables: %a"
         VS.pvs loop.lvariables.state_vars;
        printf "@.Identified index variables: %a"
         VS.pvs loop.lvariables.index_vars;
      );

    finfo.inner_funcs <- List.map translate_loop loop.inner_loops;

    let func, figu =
      match loop.ligu with
      | Some igu ->
        let in_states =
          List.map (fun info_in -> (info_in.lid, info_in.lvariables)) finfo.inner_funcs
        in
        Cil2Func.cil2func in_states loop.lvariables (loop_body loop) igu
      | None -> Cil2Func.empty_state (), None
    in

    finfo.func <- func;
    finfo.figu <- figu;
    finfo.reaching_consts <- loop.lcontext.reaching_constants;

    if !verbose then
      begin
        printf "@.Reaching constants:@.";
        IM.iter
          (fun k e -> printf "%s = %s@."
              (VS.find_by_id k loop.lvariables.state_vars).Cil.vname
              (CilTools.psprint80 Cil.dn_exp e)
          ) finfo.reaching_consts;
        let printer =
          new Cil2Func.cil2func_printer loop.lvariables
        in
        (printf "@.[for loop %i in %s]@."
           loop.lid loop.lcontext.host_function.C.vname;);
        printer#printlet func;
        printf "@.";
      end
    else ();

    finfo
  in

  List.map translate_loop sorted_lps


(**
   From intermediary representation with contained expressions to final
   functional representation.
*)
let no_sketches = ref 0;;

let func2sketch cfile funcreps =
  let rec  transform_func func_info =
    let inners = List.map transform_func func_info.inner_funcs in
    let var_set = varset_of_vs func_info.lvariables.all_vars in
    let state_vars = varset_of_vs func_info.lvariables.state_vars in

    let s_reach_consts =
      IM.fold
        (fun vid cilc m ->
           let expect_type =
             try
               (VarSet.find_by_id var_set vid).vtype
             with Not_found ->
               Bottom
           in
           match Func2Fn.conv_init_expr expect_type cilc with
           | Some e -> IM.add vid e m
           | None ->
             eprintf "@.Warning : initial value %s for %s not valid.@."
               (CilTools.psprint80 Cil.dn_exp cilc)
               (VarSet.find_by_id var_set vid).vname;
             m)
        func_info.reaching_consts IM.empty
    in

    if !verbose then
      begin
        printf "@.Reaching constants information:@.";
        IM.iter
          (fun k c ->
             printf "%s = %a@;"
               (VarSet.find_by_id state_vars k).vname
               FPretty.pp_fnexpr c)
          s_reach_consts
      end;


    let loop_body, sigu, uses_global_bounds =
      let f2f =
        let figu =
          match func_info.figu with
          | Some (iset, igu) ->
            varset_of_vs iset, igu
          | None -> failhere __FILE__ "func2sketch" "Bad for loop"
        in
        new Func2Fn.funct_builder var_set state_vars func_info.func figu
      in
      f2f#build;
      match f2f#get_funct with
      | Some (a,b) ->  a,b, f2f#get_uses_global_bounds
      | None -> failhere __FILE__ "func2sketch" "Failed in sketch building."
    in

    let index_set, _ = sigu in
    aux_vars_init ();

    let inner_indexes =
      List.map (fun pb -> mkVarExpr (VarSet.max_elt pb.scontext.index_vars)) inners
    in

    Sketch.Join.join_loop_width := !mat_w;
    let join_sk =
      Sketch.Join.build_join
        inner_indexes
        state_vars
        loop_body
    in
    (* Set the loop width for the join *)
    Sketch.Join.join_loop_width := !mat_w;
    let mless_sk =
      Sketch.Join.build_for_inner
        [FnVar (FnVariable (VarSet.max_elt index_set))]
        state_vars
        s_reach_consts
        loop_body;
    in
    incr no_sketches;
    create_boundary_variables index_set;
    (* Input size from reaching definitions, min_int dependencies,
       etc. *)
    let m_sizes =
      (* Scan the intial definitions of the state variables *)
      IM.fold
        (fun k i_def m_s ->
           match i_def with
           | FnConst c when c != Infnty && c != NInfnty -> IM.add k 0 m_s
           | FnConst c -> IM.add k 1 m_s
           | FnVar v ->
             (match v with
              | FnVariable vi -> IM.add k 0 m_s
              | FnArray (v, e) -> IM.add k (fnArray_dep_len e) m_s)
           | _ -> failhere __FILE__"func2sketch" "Unsupported intialization.")
        s_reach_consts IM.empty
    in
    let max_m_sizes = IM.fold (fun k i m -> max i m) m_sizes 0 in
    let max_m_sizes = max max_m_sizes
        (if rec_expr2 max_min_test loop_body then 1 else 0)
    in
    (if !debug then
       printf "@.Max dependency length : %i@." max_m_sizes);
    if List.length inners > 0 then
      VarSet.iter mark_outer_used (varset_of_vs func_info.lvariables.used_vars);

    (**
       Return the structure containing all the information to solve the problem.
       This structure should be containing all the information to call the solver
       and the auxiliary discovery methods.
    *)
    let lversions = SH.create 10 in
    SH.add lversions "orig" loop_body;
    {
      id = func_info.lid;
      host_function =
        (mkFuncDec
           (try check_option
               (get_fun cfile func_info.host_function.Cil.vname)
        with Failure s -> (eprintf "Failure : %s@." s;
                           failhere __FILE__ "func2sketch"
                             "Failed to get host function.")));
      loop_name = func_info.loop_name;
      scontext =
        { state_vars = state_vars;
          index_vars = index_set;
          used_vars = varset_of_vs func_info.lvariables.used_vars;
          all_vars = varset_of_vs func_info.lvariables.all_vars;
          costly_exprs = ES.empty;
        };
      min_input_size = max_m_sizes;
      uses_global_bound = uses_global_bounds;
      main_loop_body = loop_body;
      loop_body_versions = lversions;
      join_sketch = join_sk;
      memless_sketch = mless_sk;
      (* No solution for now! *)
      join_solution = FnLetExpr ([]);
      memless_solution = FnLetExpr ([]);
      init_values = IM.empty;
      identity_values = IM.empty;
      func_igu = sigu;
      reaching_consts = s_reach_consts;
      inner_functions = inners;
    }
  in
  List.map transform_func funcreps


(**
   Finds auxiliary variables necessary to parallelize the function.
   @param sketch_rep the problem representation.
   @return a new problem represention where the function and the variables
   have been modified.
*)
let find_new_variables prob_rep =
  let new_prob =
    try
      discover prob_rep
    with VariableDiscoveryError s ->
      eprintf "[ERROR] Failed to discover new variables.@.";
      raise (VariableDiscoveryError s)
  in
  (** Apply some optimization to reduce the size of the function *)
  let nlb_opt = Func2Fn.optims new_prob.main_loop_body in
  let new_loop_body =
    complete_final_state new_prob.scontext.state_vars nlb_opt
  in
  discover_save ();
  let inner_indexes =
    List.map (fun pb -> mkVarExpr (VarSet.max_elt pb.scontext.index_vars)) prob_rep.inner_functions
  in
  let join_sketch =
    (fun bnds ->
       complete_final_state new_prob.scontext.state_vars
         ((Sketch.Join.build_join
            inner_indexes
            new_prob.scontext.state_vars nlb_opt) bnds))
  in
  {
    new_prob with
    main_loop_body = new_loop_body;
    join_sketch = join_sketch;
  }

let pp_sketch ?(inner = false) ?(parent_context=None) solver fmt sketch_rep =
  let parent_context =
    if inner then
      (match parent_context with
       | Some context -> context
       | None -> failhere __FILE__ "pp_sketch" "Parent context not provided for child loop.")
    else
      mk_ctx VarSet.empty VarSet.empty
  in
  match solver.name with
  | "Rosette" ->
    begin
      copy_aux_to Sketch.auxiliary_vars;
      Sketch.pp_rosette_sketch parent_context inner fmt sketch_rep
    end
  | _ -> ()


let store_solution = Join.store_solution

let clear () =
  discover_clear ();
  Loops.clear ();
  IH.clear Sketch.auxiliary_vars
