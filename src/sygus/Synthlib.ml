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

open Cil
open Format
open Synthlib2ast
open Sylexer
open Utils
open ListTools

let parseinputs s = Syparser.file Sylexer.token (Lexing.from_string s)
let parsechan ch = Syparser.file Sylexer.token (Lexing.from_channel ch)

let printsy = sypp_sygus std_formatter

let print_file f =
  let oc = open_out f in
  sypp_sygus (Format.formatter_of_out_channel oc)

let slg_int i = SyGLiteral (SyInt i)
let slg_bool b = SyGLiteral (SyBool b)

let sl_rule name sort productions : syNTDef =
  (name, sort, productions)

(** Probably will add some intermediate language *)
let slg_plus l = SyGApp("+", l)
let slg_minus a b = SyGApp("-",[a;b])
let slg_times a b = SyGApp("*",[a;b])
let slg_ite c x y = SyGApp("ite",[c;x;y])
let slg_symb s = SyGId s

(* Macros generators *)
let sl_lia_expr ints bools : syNTDef list =
  let n1 = "LIA_Expr" in
  let n2 = "LIA_Cond" in
  [sl_rule
     "LIA_Expr"
     SyIntSort
     (ints
      @[slg_int 0; slg_int 1]
      @[slg_plus (List.map slg_symb [n1; n1])]
      @[slg_minus (slg_symb n1) (slg_symb n1)]
      @[slg_ite (slg_symb n2) (slg_symb n1) (slg_symb n1)]);
   sl_rule
     "LIA_Cond"
     SyBoolSort
     []]


let rec sort_of_ciltyp typ =
  match typ with
  | TInt _ -> SyIntSort
  | TFloat _ -> SyRealSort
  | TVoid _ -> SyIdSort "void"
  | TArray (t, en, _) -> SyArraySort (SyIntSort, sort_of_ciltyp t)
  | TPtr (t, _) -> SyArraySort(SyIntSort, sort_of_ciltyp t)
  | TComp (cinfo, _) ->
    let fields = List.map (fun field -> field.fname) cinfo.cfields in
    SyEnumSort(fields)
  | TEnum (einfo, _) ->
    let fields = List.map (fun (s,_,_) -> s) einfo.eitems in
    SyEnumSort(fields)
  | TFun (t, args, _, _) ->
    failhere __FILE__ "sort_of_ciltyp" "No type for functions."
  | TBuiltin_va_list _->
    failhere __FILE__ "sort_of_ciltyp" "No type for builtin_va_list."
  | TNamed (tinfo, _) ->
    failhere __FILE__ "sort_of_ciltyp" "No type for named type."

let sort_of_varinfo vi = sort_of_ciltyp vi.vtype

(* Some helpers to generate equivalent of recursive functions. *)
let _n_simul_recursive = ref 5

(**
   Generate a list of functions, with different arities where their
   last arguments represent the list of arguments.

   @param vname the name of the main recursion variable.
   @param vsort the sort of the main recurstion variable.
   @param fterm the term of the function of the main recursion variable.
   @param args the non-list arguments of the function including the main
   recursion variable.
   @param (listname, listsort) the name and sort of the scalar variables
   of the sequence.
   @return A list of function declaration commands.
*)

let gen_arity_defs (vname, vsort, fterm) args args_of_args
    (listname, listsort) =
  let lsizes = 0 -- (!_n_simul_recursive) in
  let build_funs_rec prev_funcs n =
    let margs =
       args @
       (List.map (fun i -> (listname^(string_of_int i)), listsort) (0 -- n))
    in
    let bodyf =
      let rec_calls_inst =
        List.fold_left
          (fun rterm (rec_vname, vsort) ->
             let rec_call_body =
               match prev_funcs with
               | [] -> SyId rec_vname
               | _ ->
                 let last_fun_name =
                   "f_"^rec_vname^"_"^(string_of_int (n-1))
                 in
                 let fun_args =
                   if rec_vname = vname then args
                   else
                     (try
                        SM.find rec_vname args_of_args
                      with Not_found ->
                        failhere __FILE__ "gen_arity_defs"
                          (sprintf "Couldn't find the args for recursive call \
                                    to %s in function f_%s." rec_vname vname))
                 in
                 let rec_args =
                   (List.map (fun (x,s) -> SyId x) fun_args) @
                   (List.map (fun i -> SyId (listname^(string_of_int i)))
                      (0 -- (n - 1)))
                 in
                 SyApp(last_fun_name, rec_args)
             in
             replace ~id:rec_vname ~by:rec_call_body ~in_term:rterm)
          fterm args
      in
      replace ~id:listname ~by:(SyId (listname^(string_of_int n)))
        ~in_term:rec_calls_inst
    in
    let nfname = "f_"^vname^"_"^(string_of_int n) in
    let funn = SyFunDefCmd(nfname, margs, vsort, bodyf) in
    prev_funcs@[funn]
  in
  List.fold_left
    build_funs_rec
    [] lsizes


(** Generate constraint for a problem. Since CVC4 does not support recursion
    we generate constraint for different sizes, callign the different functions
    with the corresponding arity.
    @param rname The name of the recursion step we are trying to
    synthesize/verify.
    @param rargs The non-list-arguments.
*)

let gen_recursion_constraints (rname, rargs, rinput) (fname, fargs, lname) =
  let gen_at_height cmd_lst i =
    let lhterm =
      let f_list_inputs = [] in
      SyApp(rname,
            [
              SyApp (fname, fargs@f_list_inputs);
            ])
    in
    let rhterm =
      let f_list_inputs =
        []
      in
      SyApp (fname, fargs@f_list_inputs)
    in
      cmd_lst@[SyConstraintCmd (SyApp("=",[lhterm; rhterm]))]
  in
  List.fold_left gen_at_height [] (1 -- !_n_simul_recursive)



(* Pre-defined functions *)

let int_max_funDefCmd =
  SyFunDefCmd("max",
              [("x", SyIntSort);("y",SyIntSort)],
              SyIntSort,
              SyApp("ite",[SyApp(">",[SyId "x"; SyId "y"]);
                          SyId "x"; SyId "y"]))

let int_min_funDefCmd =
  SyFunDefCmd("max",
              [("x", SyIntSort);("y",SyIntSort)],
              SyIntSort,
              SyApp("ite",[SyApp("<",[SyId "x"; SyId "y"]);
                           SyId "x"; SyId "y"]))

let real_max_funDefCmd =
  SyFunDefCmd("max",
              [("x", SyRealSort);("y",SyRealSort)],
              SyRealSort,
              SyApp("ite",[SyApp(">",[SyId "x"; SyId "y"]);
                          SyId "x"; SyId "y"]))

let real_min_funDefCmd =
  SyFunDefCmd("max",
              [("x", SyRealSort);("y",SyRealSort)],
              SyRealSort,
              SyApp("ite",[SyApp("<",[SyId "x"; SyId "y"]);
                           SyId "x"; SyId "y"]))
