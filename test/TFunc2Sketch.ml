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

open Beta
open Format
open Utils
open FPretty
open PpTools
open FuncTypes
module C = Canalyst
module C2F = Cil2Func
module S = Sketch


let test loopsm =
  printf "%s--------TEST Func ---> Sketch%s@." (color "red") color_default;
  SM.iter
    (fun fname vals ->
       let i0, iN = mkFnVar "i0" Integer, mkFnVar "iN" Integer in
       let vs, igu, func = vals in
       let builder = new S.Body.sketch_builder vs vs func igu in
       builder#build;
       let body_form, sigu = check_option builder#get_sketch in
       printf"%s%s%s : @; %a@." (color "green") fname color_default
         pp_fnexpr body_form;
       let join = S.Join.build_join [FnConst (CInt 0)] vs body_form in
       printf"Join : @; %a@."
         pp_fnexpr (join (mkVarExpr i0, mkVarExpr iN))
    )
    loopsm
