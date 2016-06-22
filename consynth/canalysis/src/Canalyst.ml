open Cil
open Printf
open List
open Loops2ssa
open Hashtbl

module F = Frontc
module E = Errormsg
module C = Cil
module IH = Inthash
module L2S = Loops2ssa

let debug = ref false
let verbose = ref false

let parseOneFile (fname : string) : C.file =
  let cabs, cil = Frontc.parse_with_cabs fname () in
  Rmtmps.removeUnusedTemps cil;
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
  Loops.debug := !debug; Loops.verbose := ! verbose;
  let fids = Loops.processFile cfile in
  let loops = Loops.processedLoops () in
  let loopscpy = (IH.copy loops) in
  L2S.debug := !debug;
  L2S.processFile_l2s loopscpy



let getLoops () = loops
