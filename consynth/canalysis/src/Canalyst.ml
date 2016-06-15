open Cil
open Printf
open List
open Loops
open Hashtbl

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
  let lps = Loops.processedLoops () in
  let htl = Hashtbl.length lps in
  if htl > 0 then
    begin
      printf "%d loops found. \n-- OK --\n" htl;
      Hashtbl.iter (fun k clp -> print_string (Cloop.string_of_cloop clp)) lps;
      Loops.clear ()
    end
  else
    printf "-- FAIL --\n"

