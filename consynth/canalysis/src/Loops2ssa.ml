open Cil
open Loops

(** Main entry point *)
let processFile_l2s cfile =
  ignore(Loops.processFile cfile);
  let loops = Loops.processedLoops () in
  loops
