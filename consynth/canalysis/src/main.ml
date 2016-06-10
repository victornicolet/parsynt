open Cil
open Printf

module F = Frontc
module E = Errormsg
module C = Cil

let parseOneFile (fname : string) : C.file =
  let cabs, cil = Frontc.parse_with_cabs fname () in
  Rmtmps.removeUnusedTemps cil;
  cil


let main () =
  C.insertImplicitCasts := false;
  C.lineLength := 1000;
  C.warnTruncate := false;
  Cabs2cil.doCollapseCallCast := true;
  let usageMsg = "Usage : canalyze [options] source-files" in
  let fileName = "todo" in
  let cfile = parseOneFile fileName in
  Cfg.computeFileCFG cfile;
  
