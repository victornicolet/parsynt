open Cil

(**
   The states variables is a list of variables we have computed 
   before.
   TODO : differentiate shareable variables and other variables.
*)
var state : Cil.varinfo list
(** 
    A loop body is a list of instructions, where each instruction
    is an assignment to a state varaiable.
*)
var loop_body : Cil.instr list

var loop_bounds : unit
(** 
    The sketch compilation function outputs a sketch to be given
    to Rosette.
*)
var compile_sketch : unit

