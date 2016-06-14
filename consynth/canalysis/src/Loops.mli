open Cil
open String

type defsMap = Reachingdefs.IOS.t Reachingdefs.IH.t

module Cloop : sig
  type t = {
    sid: int;
    mutable parentLoops : int list;
    mutable parentFunction : Cil.varinfo;
    mutable calledFunctions : varinfo list;
    mutable definedInVars : defsMap option;
    mutable usedOutVars : varinfo list;
    mutable inNormalForm : bool;
    mutable inSsaForm : bool;
    mutable hasBreaks : bool;
  }
  val create: int -> Cil.varinfo -> t
  val string_of_cloop: t -> String.t
end

val processFile: Cil.file -> unit
