open Sketch
open PpHelper
open Format
open Utils
open Variable

module E = Errormsg
module C = Cil
module Cl = Findloops.Cloop
module A = AnalyzeLoops

let debug = ref false
let verbose = ref false

let parseOneFile (fname : string) : C.file =
  let cabs, cil =
    try
      Frontc.parse_with_cabs fname ()
    with
      Errormsg.Error ->
        failwith "Error while parsing input file,\
the filename might contain errors"
  in
  cil


let processFile fileName =
  C.insertImplicitCasts := false;
  C.lineLength := 1000;
  C.warnTruncate := false;
  Cabs2cil.doCollapseCallCast := true;
  let cfile = parseOneFile fileName in
  Cfg.computeFileCFG cfile;
  Deadcodeelim.dce cfile;
  Findloops.debug := !debug;
  Findloops.verbose := !verbose;
  Rmtmps.removeUnusedTemps cfile;
  let loops, _ = Findloops.processFile cfile in
  loops


(**
   Returns a tuple with :
   - list of variables ids that a read in the loop.
   - list of state variables (written)
   - the set of variables defined in the loop.
   - the function representing the body of the loop.
*)
type func_info =
  int list * int list * Usedef.VS.t *
    Cil2Func.letin * (Cil.constant Utils.IM.t)

type sketch_info =
  int list * int list * Usedef.VS.t * SketchTypes.sklet *
     SketchTypes.sklet * (SketchTypes.skExpr Utils.IM.t)


let cil2func loops =
  Cil2Func.init loops;
  let sorted_lps = A.transform_and_sort loops in
  List.map
    (fun cl ->
      let stmt = C.mkBlock(cl.Cl.new_body) in
      let r, w = cl.Cl.rwset in
      let stv = w in
      let vars = VSOps.vs_of_defsMap cl.Cl.defined_in in
      let func = Cil2Func.cil2func stmt stv in
      let reaching_consts = cl.Cl.constant_in in
      if !verbose then
        begin
          (printf "%s[test for loop %i in %s failed]%s@."
             (color "red") cl.Cl.sid cl.Cl.host_function.C.vname default;);
          Cil2Func.printlet (stv, func);
          printf "@.";
        end;
      (VSOps.vids_of_vs r, VSOps.vids_of_vs stv, vars, func, reaching_consts))
    sorted_lps

let func2sketch funcreps =
  List.map
    (fun (ro_vars_ids, state_vars_ids, var_set, func, reach_consts) ->
      let reach_consts =
        IM.mapi
          (fun vid cilc ->
            let expect_type =
              try
                (SketchTypes.symb_type_of_ciltyp
                   ((VSOps.find_by_id vid var_set).Cil.vtype))
              with Not_found ->
                SketchTypes.Bottom
            in
            Sketch.Body.convert_const expect_type cilc)
          reach_consts
      in
      let state_vars = VSOps.subset_of_list state_vars_ids var_set in
      let loop_body = Sketch.Body.build func state_vars in
      let join_body = Sketch.Join.build loop_body state_vars in
      (ro_vars_ids, state_vars_ids, var_set,
       loop_body, join_body, reach_consts))
    funcreps

let pp_sketch = Sketch.pp_rosette_sketch
