open Cil
open Inthash

module VS = Utils.VS

module RWSet : sig
    val computeRWs: Cil.stmt -> VS.t -> VS.t * VS.t
end
