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

(** General settings *)
val project_dir: string
val output_dir:string ref
val get_conf_string: string -> string
val get_conf_int: string -> int
val template:string->string
(** Builtin variables *)
type builtins =
  | Min_Int
  | Max_Int
  | False
  | True
val is_builtin_var: string -> bool
val get_builtin: string -> builtins
(** Verification parameters *)
val verification_parameters : (int * int * int) list
(* Naming conventions *)
val inner_loop_func_name : string -> int -> string
val is_inner_loop_func_name : string -> bool
val is_inner_join_name : string -> bool
val id_of_inner_loop: string -> int
val join_name: string -> string
val seq_name: string -> string
val strip_contextual_prefix: string -> string
(* Solvers *)
type solver = { name: string; extension: string; execname: string;}
val rosette : solver
val cvc4 : solver
