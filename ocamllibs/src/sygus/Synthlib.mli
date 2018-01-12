(**
   This file is part of Parsynt.

   Author: Victor Nicolet <victorn@cs.toronto.edu>

    Parsynt is free software: you can redistribute it and/or modify
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

open Synthlib2ast

val parseinputs : string -> sygusFile
val parsechan : in_channel -> sygusFile
val printsy : sygusFile -> unit

val sort_of_varinfo : Cil.varinfo -> sySort

val gen_arity_defs: (symbol * sySort) -> (symbol * sySort * syTerm) ->
  (symbol * sySort) list -> symbol * sySort -> (symbol * syCmd) list
