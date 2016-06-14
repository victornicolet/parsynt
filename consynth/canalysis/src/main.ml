open Cil
open Printf
open List
open Loops

module F = Frontc
module E = Errormsg
module C = Cil

let parseOneFile (fname : string) : C.file =
  let cabs, cil = Frontc.parse_with_cabs fname () in
  Rmtmps.removeUnusedTemps cil;
  cil


let processFile fileName =
  C.insertImplicitCasts := false;
  C.lineLength := 1000;
  C.warnTruncate := false;
  Cabs2cil.doCollapseCallCast := true;
  let cfile = parseOneFile fileName in
  Cfg.computeFileCFG cfile;
  Deadcodeelim.dce cfile;
  Loops.processFile cfile;
  printf "-- OK --\n"

