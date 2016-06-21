(**
    Custom dataflow analysis not provided by Cil.
    Main components :
    - Read/Write set of a body
*)
open Hashtbl
open String
open Cil

module IH = Inthash
module U = Utils
module VS = U.VS


(** Here we do not use Cil's Dataflow framework *)

module RWSet = struct

  let verbose = ref false

  let prws u d =
	print_endline "--Uses";
	VS.iter U.ppv u;
	print_endline "Defs";
	VS.iter U.ppv d

  let computeRWs (loop : Cil.stmt) (fnames : VS.t) : VS.t * VS.t  =
	Usedef.onlyNoOffsetsAreDefs := true;
	let _u, _d = Usedef.computeDeepUseDefStmtKind loop.skind in
	let u, d = VS.diff _u fnames, VS.diff _d fnames in
	if !verbose then prws u d;
	u, d
end
