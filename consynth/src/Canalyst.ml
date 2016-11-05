open Sketch
open PpHelper
open Format
open Utils
open SError
open SymbExe
open VariableDiscovery

module E = Errormsg
module C = Cil
module Cl = Findloops.Cloop
module A = AnalyzeLoops
module T = SketchTypes

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
  let decl_header = parseOneFile ((Sys.getcwd ())^"/templates/decl_header.h") in
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
  string * int list * VS.t * VS.t *
  Cil2Func.letin * figu * (Cil.constant Utils.IM.t)

(** Sketch info type :
    - subset of read variables
    - subset of written variables,
    - set of variables in the function
    - body of the function
    - init, guard and update of the enclosing loop
    - sketch of the join.
*)
type sigu = VS.t * (T.sklet * T.skExpr * T.sklet)

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
       let loop_ident = cl.Cl.host_function.C.vname in
       let stmt = C.mkBlock(cl.Cl.new_body) in
       let r, w = cl.Cl.rwset in
       let vars = VSOps.vs_of_defsMap cl.Cl.defined_in in
       let stv = VS.filter (fun v -> VS.mem v vars) w in
       let func, figu = Cil2Func.cil2func stv stmt (i,g,u) in
       let reaching_consts = cl.Cl.constant_in in
       if !verbose then
         begin
           (printf "@.%s[test for loop %i in %s failed]%s@."
              (color "red") cl.Cl.sid cl.Cl.host_function.C.vname default;);
           Cil2Func.printlet (stv, func);
           printf "@.";
         end;
       (loop_ident,
        VSOps.vids_of_vs r, stv, vars,
        func, figu,
        reaching_consts))
    sorted_lps

type sketch_rep =
  {
    loop_name : string;
    ro_vars_ids : int list;
    state_vars : VS.t;
    var_set : VS.t;
    loop_body : T.sklet;
    join_body : T.sklet;
    sketch_igu : sigu;
    reaching_consts : T.skExpr IM.t
  }

let func2sketch funcreps =
  List.map
    (fun (loop_ident,
          ro_vars_ids, state_vars, var_set, func, figu, reach_consts) ->
      let reach_consts =
        IM.mapi
          (fun vid cilc ->
            let expect_type =
              try
                (T.symb_type_of_ciltyp
                   ((VSOps.find_by_id vid var_set).Cil.vtype))
              with Not_found ->
                T.Bottom
            in
            Sketch.Body.convert_const expect_type cilc)
          reach_consts
      in
      let loop_body, sigu = Sketch.Body.build var_set state_vars func figu in

      IH.clear SketchJoin.auxiliary_variables;

      let join_body = Sketch.Join.build state_vars loop_body in
      {
        loop_name = loop_ident;
        ro_vars_ids = ro_vars_ids;
        state_vars = state_vars;
        var_set =  var_set;
        loop_body = loop_body;
        join_body = join_body;
        sketch_igu = sigu;
        reaching_consts = reach_consts;
      })
    funcreps

let find_new_variables sketch_rep =
  let new_state, nlb =
    discover sketch_rep.state_vars sketch_rep.loop_body sketch_rep.sketch_igu
  in
  (** Apply some optimization to reduce the size of the function *)
  let nlb_opt = Sketch.Body.optims nlb in
  let new_loop_body =
    SketchTypes.complete_final_state new_state nlb_opt
  in

  IH.copy_into VariableDiscovery.discovered_aux
    SketchJoin.auxiliary_variables;

  let join_body =
    SketchTypes.complete_final_state
      new_state
      (Sketch.Join.build new_state nlb_opt)
  in

  {
    sketch_rep with
    state_vars = new_state;
    var_set =  VS.union new_state sketch_rep.var_set;
    loop_body = new_loop_body;
    join_body = join_body;
  }

  let pp_sketch fmt sketch_rep =
  IH.copy_into VariableDiscovery.discovered_aux Sketch.auxiliary_vars;
  Sketch.pp_rosette_sketch fmt
    (sketch_rep.ro_vars_ids,
     VSOps.vids_of_vs sketch_rep.state_vars,
     sketch_rep.var_set,
     sketch_rep.loop_body,
     sketch_rep.join_body,
     sketch_rep.sketch_igu,
     sketch_rep.reaching_consts)
