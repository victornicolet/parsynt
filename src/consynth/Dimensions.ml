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
open Beta

let iterations_limit = Conf.get_conf_int "loop_finite_limit"

let inner_iterations_limit = Conf.get_conf_int "inner_loop_finite_limit"

let mat_w = ref 0
let mat_h = ref 0

  let set_default () =
  mat_w := inner_iterations_limit;
mat_h := iterations_limit

  let set_large_square () =
  mat_w := iterations_limit;
mat_h := iterations_limit

  let set_small_square () =
  mat_w := inner_iterations_limit;
mat_h := inner_iterations_limit

  let reset_matdims() =
set_default ()

let width () = !mat_w
let height () = !mat_h
let dims () = (!mat_h , !mat_w)

let bounds (fixed : bool) (sketch : prob_rep) : fnExpr * fnExpr =
  let ist, ien = get_bounds sketch in
  if fixed then FnConst(CInt 0), FnConst(CInt (width ()))
  else mkVarExpr ist, mkVarExpr ien
