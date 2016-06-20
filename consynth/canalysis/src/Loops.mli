open Cil
open String
open Utils

val verbose : bool ref
val debug : bool ref

type defsMap = (Utils.VS.elt * Reachingdefs.IOS.t option)  Inthash.t
type forIGU = (Cil.instr * Cil.exp * Cil.instr)
val indexOfIGU: forIGU -> VS.t

module Cloop : sig
  type t = {
    sid: int;
    mutable loopStatement : Cil.stmt;
    mutable loopIGU : forIGU option;
    mutable parentFile : Cil.file;
    mutable parentLoops : int list;
    mutable parentFunction : Cil.varinfo;
    mutable calledFunctions : Cil.varinfo list;
    mutable definedInVars : defsMap;
    mutable usedOutVars : Cil.varinfo list;
    mutable rwset : int list * int list * int list;
    mutable inNormalForm : bool;
    mutable inSsaForm : bool;
    mutable hasBreaks : bool;
  }
  val create: Cil.stmt -> Cil.varinfo -> Cil.file -> t
  val string_of_cloop: t -> String.t
end

val processFile: Cil.file -> int list
val processedLoops: unit -> Cloop.t Inthash.t
val clear : unit -> unit
