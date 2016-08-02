open Cil
open String
open Utils

val verbose : bool ref
val debug : bool ref

type defsMap = (Utils.VS.elt * Reachingdefs.IOS.t option)  Inthash.t
type forIGU = (Cil.instr * Cil.exp * Cil.instr)
val index_of_igu: forIGU -> VS.t
val check_igu: forIGU -> bool

module Cloop : sig
  type t = {
    sid: int;
    mutable old_loop_stmt : Cil.stmt;
    mutable new_body : Cil.stmt list;
    mutable loop_igu : forIGU option;
    mutable parent_file : Cil.file;
    mutable parent_loops : int list;
    mutable inner_loops : stmt list;
    mutable host_function : Cil.varinfo;
    mutable called_functions : Cil.varinfo list;
    mutable defined_in : defsMap;
    mutable used_out : Cil.varinfo list;
    mutable rwset : Utils.VS.t * Utils.VS.t;
    mutable has_breaks : bool;
  }
  val state: t -> Utils.VS.t
  val create: Cil.stmt -> Cil.varinfo -> Cil.file -> t
  val string_of_cloop: t -> String.t
end

val processFile: Cil.file -> Cloop.t Utils.IM.t * int list
val processedLoops: unit -> Cloop.t Inthash.t
val clear : unit -> unit
