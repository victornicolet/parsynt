open Cil
open Hashtbl
open Sketch
open Utils

module F = Frontc
module E = Errormsg
module C = Cil
module IH = Inthash

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
