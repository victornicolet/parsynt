open Cil
open Format
open Synthlib2ast
open Sylexer
open Utils
open ListTools

let parseinputs s = Syparser.file Sylexer.token (Lexing.from_string s)
let parsechan ch = Syparser.file Sylexer.token (Lexing.from_channel ch)

let printsy = sypp_sygus std_formatter

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


(* Some helpers to generate equivalent of recusrive functions. *)
let _n_simul_recursive = ref 5
(* Generate a list of functions, with different arities where their
   last arguments represent the list of arguments. *)
let gen_arity_defs (fname, sort) (vname, vsort, vterm)
    nonlist_args (listname, listsort) =
  let lsizes = 0 -- (!_n_simul_recursive) in
  let build_funs_rec prev_funcs n =
    let margs =
       nonlist_args @
       (List.map (fun i -> (listname^(string_of_int i)), listsort) (0 -- n))
    in
    let bodyf =
      let rec_call =
        match prev_funcs with
        | [] -> SyId vname
        | _ ->
          let last_fun_name, _ = last prev_funcs
          in
          let rec_args =
            (List.map (fun (x,s) -> SyId x) nonlist_args) @
            (List.map (fun i -> SyId (listname^(string_of_int i)))
               (0 -- (n - 1)))
          in
          SyApp(last_fun_name, rec_args)
      in
      replace ~id:listname ~by:(SyId (listname^(string_of_int n)))
        ~in_term:(replace ~id:vname ~by:rec_call ~in_term:vterm)
    in
    let nfname = fname^"_"^(string_of_int n) in
    let funn = SyFunDefCmd(nfname, margs, sort, bodyf) in
    prev_funcs@[(nfname, funn)]
  in
  List.fold_left
    build_funs_rec
    [] lsizes
