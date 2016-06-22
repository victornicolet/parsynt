(**
    This file contains a description of the loop with all the information
    needed to produce the sketch that will then be synthesized by Rosette.
*)
open Cil
open Loops
module L2S = Loops2ssa
module F = L2S.Floop
module IH = Inthash

let floops = IH.create 10

let processLoops (fmap : F.t Inthash.t) =
  ()

let normIGU (fl : F.t) =
  let (i, g, u) = fl.F.igu in
  fl

let 
