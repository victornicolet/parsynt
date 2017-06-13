open Sketch
open Format
open Utils
open Utils.PpTools
open SError
open SketchTypes
open SymbExe
open VariableDiscovery

module E = Errormsg
module C = Cil
module Cl = Findloops.Cloop
module A = AnalyzeLoops

let debug = ref false
let verbose = ref false



let parseOneFile (fname : string) : C.file =
  try
    Frontc.parse fname ()
  with
    Errormsg.Error ->
    failwith "Error while parsing input file,\
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
    parseOneFile (Conf.project_dir^"/templates/decl_header.h")
  in
  let cfile = Mergecil.merge [decl_header; parseOneFile fileName] "main" in
  Cfg.computeFileCFG cfile;
  (*  Deadcodeelim.dce cfile; *)
  Findloops.debug := !debug;
  Findloops.verbose := !verbose;
  let loops, _ = Findloops.processFile cfile in
  loops


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
  string * Cil.fundec * int list * VS.t * VS.t *
  Cil2Func.letin * figu * (Cil.constant Utils.IM.t)

(** Sketch info type :
    - subset of read variables
    - subset of written variables,
    - set of variables in the function
    - body of the function
    - init, guard and update of the enclosing loop
    - sketch of the join.
*)
type sigu = VS.t * (sklet * skExpr * sklet)

(** Create unique identifiers for each loop - each problem we
    have to solve *)
let loop_idents_index = ref 0

let loop_idents = ref []

let rec new_loop_ident fun_name =
  if List.mem fun_name !loop_idents then
    (let new_ident = fun_name ^ "_" ^ (string_of_int !loop_idents_index) in
     incr loop_idents_index;
     new_loop_ident new_ident)
  else
    (loop_idents := fun_name::(!loop_idents);
     fun_name)

(** From cil loop bodies to intermediary function representation.
        This step only translates the control-flow of the input C program,
        the expressions will be translated later *)
let cil2func loops =
  Cil2Func.init loops;
  let sorted_lps = A.transform_and_sort loops in
  List.map
    (fun cl ->
       (** Index *)
       let i,g,u =
         try
           check_option cl.Cl.loop_igu
         with Failure s ->
           skip_exn "Couldn't use index form in loop.";
       in
       let loop_ident = new_loop_ident cl.Cl.host_function.C.vname in
       let stmt = C.mkBlock(cl.Cl.new_body) in
       let r, w = cl.Cl.rwset in
       let vars = remove_reserved_vars (Cl.getAllVars cl) in
       let stv = Cl.getStateVars cl in
       let func, figu = Cil2Func.cil2func (VS.union vars w) stv stmt (i,g,u) in
       let reaching_consts = cl.Cl.constant_in in
       if !verbose then
         let printer = new Cil2Func.cil2func_printer vars stv in
         (printf "@.%s[test for loop %i in %s failed]%s@."
            (color "red") cl.Cl.sid cl.Cl.host_function.C.vname color_default;);
         printer#printlet func;
         printf "@.";
       else ();
       (loop_ident,
        Cl.getParentFundec cl,
        VSOps.vids_of_vs r, stv, vars,
        func, figu,
        reaching_consts))
    sorted_lps


let no_sketches = ref 0;;

let func2sketch funcreps =
  List.map
    (fun (loop_ident, host_function,
          ro_vars_ids, state_vars, var_set, func, figu, reach_consts) ->
      let reach_consts =
        IM.fold
          (fun vid cilc m ->
             let expect_type =
               try
                 (T.type_of_ciltyp
                    ((VSOps.find_by_id vid var_set).Cil.vtype))
               with Not_found ->
                 T.Bottom
             in
             match Sketch.Body.conv_init_expr expect_type cilc with
             | Some e -> IM.add vid e m
             | None ->
               eprintf "@.Warning : initial value %s for %s not valid.@."
                 (CilTools.psprint80 Cil.dn_exp cilc)
                 (VSOps.find_by_id vid var_set).Cil.vname;
               m)
          reach_consts IM.empty
      in
      let sketch_obj =
        new Sketch.Body.sketch_builder var_set state_vars func figu
      in
      sketch_obj#build;
      let loop_body, sigu =
        match sketch_obj#get_sketch with
        | Some (a,b) -> a,b
        | None -> failwith "Failed in sketch building."
      in
      let index_set, _ = sigu in
      IH.clear SketchJoin.auxiliary_variables;
      let join_body = Sketch.Join.build state_vars loop_body in
      incr no_sketches;
      create_boundary_variables index_set;
      (** Clean the variables sets : keep only variables used in the
          loop body *)
      let bound_in_sklet, used_vars_set = used_in_sklet loop_body in
      (* Input size from reaching definitions, min_int dependencies,
         etc. *)
      let m_sizes =
        (* Scan the intial definitions of the state variables *)
        IM.fold
          (fun k i_def m_s ->
             match i_def with
             | SkConst c when c != Infnty && c != NInfnty -> IM.add k 0 m_s
             | SkConst c -> IM.add k 1 m_s
             | SkVar v ->
              (match v with
                | SkVarinfo vi -> IM.add k 0 m_s
                | SkArray (v, e) -> IM.add k (skArray_dep_len e) m_s
                | _ -> raise Tuple_fail)
             | _ -> failwith "Unsupported intialization.")
          reach_consts IM.empty
      in
      let max_m_sizes = IM.fold (fun k i m -> max i m) m_sizes 0 in
      let max_m_sizes = max max_m_sizes
          (if uses_max_min loop_body then 1 else 0)
      in
      printf "@.Max dependency length : %i@." max_m_sizes;
      {
        id = !no_sketches;
        host_function = host_function;
        loop_name = loop_ident;
        ro_vars_ids = ro_vars_ids;
        scontext =
          { state_vars = state_vars;
            index_vars = index_set;
            used_vars = used_vars_set;
            all_vars = var_set;
            costly_exprs = ES.empty;
          };
        min_input_size = max_m_sizes;
        uses_global_bound = sketch_obj#get_uses_global_bounds;
        loop_body = loop_body;
        join_body = join_body;
        join_solution = SkLetExpr ([]);
        init_values = IM.empty;
        sketch_igu = sigu;
        reaching_consts = reach_consts;
      })
    funcreps

let find_new_variables sketch_rep =
  let new_sketch = discover sketch_rep in
  (** Apply some optimization to reduce the size of the function *)
  let nlb_opt = Sketch.Body.optims new_sketch.loop_body in
  let new_loop_body =
    T.complete_final_state new_sketch.scontext.state_vars nlb_opt
  in
  IH.copy_into VariableDiscovery.discovered_aux_alltime
    SketchJoin.auxiliary_variables;

  let join_body =
    T.complete_final_state new_sketch.scontext.state_vars
      (Sketch.Join.build new_sketch.scontext.state_vars nlb_opt)
  in
  {
    new_sketch with
    loop_body = new_loop_body;
    join_body = join_body;
  }

let pp_sketch fmt sketch_rep =
  IH.copy_into VariableDiscovery.discovered_aux_alltime Sketch.auxiliary_vars;
  Sketch.pp_rosette_sketch fmt sketch_rep
