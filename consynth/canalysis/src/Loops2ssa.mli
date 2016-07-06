open Loops
open Prefunc

val debug: bool ref

module Floop : sig
  type t = {
    sid: int;
    mutable igu: forIGU;
    mutable body : preFunc Inthash.t;
    mutable parentLoops : int list;
    mutable state : int list;
    mutable indexes : int list;
    mutable usedOutVars: Cil.varinfo list;
    mutable allVars: VS.t ;
  }

  val fromCloop: int -> Cloop.t -> t
end

val floops : Floop.t Inthash.t
val processFile_l2s : Loops.Cloop.t Inthash.t -> Floop.t Inthash.t
val clear: unit -> unit
