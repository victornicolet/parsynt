open Cil
open Inthash

module VS = Utils.VS


module RWSet : sig
  val verbose : bool ref
  val computeRWs: Cil.stmt -> VS.t -> VS.t * VS.t
end
