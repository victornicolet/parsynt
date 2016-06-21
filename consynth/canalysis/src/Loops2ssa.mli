open Loops

val debug: bool ref

type preFunc = 
  | Empty
  | Container of Cil.exp
  | FBinop of Cil.binop * preFunc * preFunc
  | FUnop of Cil.unop * preFunc
  | ForLoop of preFunc * Loops.forIGU * Cil.exp list * preFunc
  | Guarded of preFunc * preFunc * preFunc


module Floop : sig 
    type t = {
      sid: int;
      mutable igu: forIGU;
      mutable body : preFunc Inthash.t;
      mutable state : int list;
      mutable parentLoops : int list;
      mutable definedInVars: defsMap;
      mutable usedOutVars: Cil.varinfo list;
      mutable allVars: Utils.VS.t ;
    }

    val fromCloop: int -> Cloop.t -> t
end

val floops : Floop.t Inthash.t
val processFile_l2s : Loops.Cloop.t Inthash.t -> Floop.t Inthash.t
val clear: unit -> unit
