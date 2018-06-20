(**
   This file is part of Parsynt.

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
open Expressions
open Format
open FnPretty
open Fn
open SymbExe
open Utils
open VUtils


let find_accumulator (xinfo : exec_info ) (ne : fnExpr) : AuxSet.t -> AuxSet.t =
  AuxSet.filter
    (fun aux ->
       let xinfo' =
         {xinfo with context = {xinfo.context with state_vars = VarSet.empty}}
       in
       let replace_cell aux j e =
         match aux.aexpr with
         | FnVector el ->
           replace_expression
             (mkVarExpr ~offsets:[FnConst (CInt j)] aux.avar)
             (el >> j)
             e
         | ex ->
           replace_expression
             (mkVarExpr ~offsets:[FnConst (CInt j)] aux.avar)
             ex
             e
       in
       let unfold_op e = fst (unfold_expr xinfo' e) in
       let e_unfolded =
         match aux.afunc with
         | FnVector el ->
           FnVector(List.mapi (fun i e -> replace_cell aux i (unfold_op e)) el)
         | e ->
           replace_expression (mkVarExpr aux.avar) aux.aexpr (unfold_op e)
       in
       printf "@[<v 4>Accumulation?@;%a==@;%a@.%b@]@."
         cp_fnexpr e_unfolded cp_fnexpr ne (e_unfolded @= ne);
       e_unfolded @= ne)
