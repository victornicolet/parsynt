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

open FuncTypes
open Utils

(**
   Replaces calls to inner loop function in the outer loop
    by a simplified version using the join of the inner loop or the memoryless
    version of the loop when possible.
   @param problem The current problem, where nothing is solved.
   @param inner_loops A map from loop ids to structures containing the
   information on the inner loop.
   @return The problem where inner loop info has been updated and the outer body
   has been simplified using all the information possible and updated variables
   with new sequences representing inner loop's outputs.
*)

let replace_by_join problem inner_loops =
  let replace lid in_info (lbody, ctx) = lbody, ctx
  in
  IM.fold replace inner_loops (problem.loop_body, problem.scontext)
