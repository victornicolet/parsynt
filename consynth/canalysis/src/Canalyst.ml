open Cil
open Hashtbl
open Sketch
open Utils

module F = Frontc
module E = Errormsg
module C = Cil
module IH = Inthash
module L2S = Loops2ssa

let debug = ref false
let verbose = ref false

let parseOneFile (fname : string) : C.file =
  let cabs, cil = Frontc.parse_with_cabs fname () in
  cil

let loops = IH.create 10

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
  ignore(Loops.processFile cfile);
  IHTools.add_all loops (Loops.processedLoops ());
  let loopscpy = (IH.copy loops) in
  L2S.debug := !debug;
  let floops = L2S.processFile_l2s loopscpy in
  let sketchSet = IH.create 10 in
  IH.iter (fun k v ->
    IH.add sketchSet k (build_sketch v)) floops;
  IH.iter (fun k sketch -> SPretty.printSketch sketch) sketchSet;
  floops



let getLoops () = loops
