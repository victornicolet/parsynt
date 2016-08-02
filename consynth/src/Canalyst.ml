open Sketch
open PpHelper
open Format
open Utils

module E = Errormsg
module C = Cil
module Cl = Loops.Cloop

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
  Loops.debug := !debug;
  Loops.verbose := !verbose;
  Rmtmps.removeUnusedTemps cfile;
  let loops, _ = Loops.processFile cfile in
  loops


(**
   Returns a tuple with :
   - list of variables ids that a read in the loop.
   - list of state variables (written)
   - the set of variables defined in the loop.
   - the function representing the body of the loop.
*)
let cil2func loops =
  Cil2Func.init loops;
  IM.map
    (fun cl ->
      let stmt = C.mkBlock(cl.Cl.new_body) in
      let r, w = cl.Cl.rwset in
      let stv = w in
      let vars = VSOps.vs_of_defsMap cl.Cl.defined_in in
      let func = Cil2Func.cil2func stmt stv in
      if !verbose then
        begin
          (printf "%s[test for loop %i in %s failed]%s@."
             (color "red") cl.Cl.sid cl.Cl.host_function.C.vname default;);
          Cil2Func.printlet (stv, func);
          printf "@.";
        end;
      (VSOps.vids_of_vs r, VSOps.vids_of_vs stv, vars, func))
    loops

let func2sketch funcreps =
  IM.map
    (fun (ro_vars_ids, state_vars_ids, var_set, func) ->
      let state_vars = VSOps.subset_of_list state_vars_ids var_set in
      let loop_body = Sketch.build_body func state_vars in
      let join_body = Sketch.build_join loop_body state_vars in
      (ro_vars_ids, state_vars_ids, var_set, loop_body, join_body))
    funcreps

let pp_sketch = Sketch.pp_rosette_sketch
