open Cil
open String
open Utils

val verbose : bool ref
val debug : bool ref

type defsTable = (Utils.VS.elt * Reachingdefs.IOS.t option)  IH.t
type forIGU = (Cil.instr * Cil.exp * Cil.instr)
val index_of_igu: forIGU -> VS.t
val check_igu: forIGU -> bool

type loop_rep = {
  mutable lstmt : Cil.stmt;
  mutable lanalyzed : bool;
  mutable lsids : Cil.stmt IH.t;
}

module Cloop : sig
  type t = {
    sid: int;
    mutable old_loop : loop_rep;
    mutable new_loop : loop_rep;
    mutable loop_igu : forIGU option;
    mutable parent_file : Cil.file;
    mutable parent_loops : int list;
    mutable inner_loops : stmt list;
    mutable host_function : Cil.varinfo;
    mutable called_functions : VS.t;
    mutable reaching_definitions : defsTable;
    mutable reaching_constant_definitions : Cil.exp IM.t;
    mutable live_variables : VS.t;
    mutable rwset : Utils.VS.t * Utils.VS.t;
    mutable has_breaks : bool;
  }

  val all_vars : t -> VS.t
  val create: Cil.stmt -> Cil.varinfo -> Cil.file -> t
  val new_body: t -> Cil.stmt list
  val parent_fundec : t -> Cil.fundec
  val state : t -> VS.t
  val __str__: t -> String.t
end

val return_exprs : exp IH.t
val processFile: Cil.file -> Cloop.t Utils.IM.t * int list
val processedLoops: unit -> Cloop.t IH.t
val clear : unit -> unit
