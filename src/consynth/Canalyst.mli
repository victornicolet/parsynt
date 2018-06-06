(**
   This file is part of Parsynt.

    Foobar is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Parsynt is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Parsynt.  If not, see <http://www.gnu.org/licenses/>.
*)

val verbose : bool ref

type figu = Utils.VS.t * (Cil2Func.letin * Cil2Func.expr * Cil2Func.letin)
type varset_info = int list * int list * Utils.VS.t
type func_info =
  {
    host_function : Cil.varinfo;
    mutable func : Cil2Func.letin;
    mutable figu : figu option;
    lid : int;
    loop_name : string;
    lvariables : Loops.variables;
    mutable reaching_consts : Cil.exp Utils.IM.t;
    mutable inner_funcs : func_info list;
  }

val parseOneFile: string -> Cil.file
val processFile: string -> Cil.file * Loops.loop_info Utils.IM.t
val cil2func : Cil.file -> Loops.loop_info Utils.IM.t -> func_info list
val func2sketch: Cil.file -> func_info list -> FuncTypes.prob_rep list
val find_new_variables : FuncTypes.prob_rep -> FuncTypes.prob_rep
val pp_sketch: ?inner:bool -> ?parent_context:FuncTypes.context option->
  Conf.solver -> Format.formatter -> FuncTypes.prob_rep -> unit
val fetch_solution:
  ?solver:Conf.solver ->
  ?inner:bool->
  ?parent_ctx:(FuncTypes.context option) ->
  FuncTypes.prob_rep -> float * FuncTypes.prob_rep option

val store_solution: FuncTypes.prob_rep option -> unit
val clear: unit -> unit
