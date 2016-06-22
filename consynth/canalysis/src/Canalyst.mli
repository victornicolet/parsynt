open Cil

val processFile: string -> Loops2ssa.Floop.t Inthash.t
val getLoops: unit -> Loops.Cloop.t Inthash.t
