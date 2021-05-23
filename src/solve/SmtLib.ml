open Base
open Utils
open Sexplib

module OC = Stdio.Out_channel
module IC = Stdio.In_channel


type numeral = int


type smtSymbol =
  | SSimple of string
  | SQuoted of string


let symb_equal s1 s2 =
  match s1, s2 with
  | SSimple name1, SSimple name2 -> String.equal name1 name2
  | SQuoted name1, SQuoted name2 -> String.equal name1 name2
  | _, _ -> false


let str_of_symb s1 =
  match s1 with
  | SSimple s -> s
  | SQuoted s -> "`"^s


type smtIndex =
  | INum of numeral
  | ISym of smtSymbol


type smtIdentifier =
  | Id of smtSymbol
  | IdC of smtSymbol * smtIndex list


type smtSort =
  | SmtSort of smtIdentifier
  | Comp of smtIdentifier * smtSort list


type smtSortedVar = smtSymbol * smtSort


type smtQualIdentifier =
  | QI of smtIdentifier
  | QIas of smtIdentifier * smtSort


type smtAttribute =
  | ASymb of string
  | ASymbVal of string * string


type smtPattern =
  | Pat of smtSymbol
  | PatComp of smtSymbol * smtSymbol list


type smtSpecConstant =
  | SCNumeral of numeral
  | SCDecimal of numeral * int * numeral
  | SCHexaDecimal of string
  | SCBinary of bool list
  | SCString of string

type smtTerm =
  | TSpecConst of smtSpecConstant
  | TQualdId of smtQualIdentifier
  | TApp of smtQualIdentifier * smtTerm list
  | TLet of var_binding list * smtTerm
  | TForall of smtSortedVar list * smtTerm
  | TExists of smtSortedVar list * smtTerm
  | TMatch of smtTerm * match_case list
  | TAnnot of smtTerm * smtAttribute list

and match_case = smtPattern * smtTerm
and var_binding = smtSymbol * smtTerm

type smdSortDec = smtSymbol * numeral

type smtSelectorDec = smtSymbol * smtSort

type smtConstructorDec = smtSymbol * smtSelectorDec list

type datatype_dec =
  | DDConstr of smtConstructorDec list
  | DDPar of smtSymbol list * smtConstructorDec list

type func_dec = smtSymbol * smtSortedVar list * smtSort

type func_def = smtSymbol * smtSortedVar list * smtSort * smtTerm

type prop_literal =
  | PL of smtSymbol
  | PLNot of smtSymbol

type info_flag = int

type solver_option = string * string


type command =
  | Assert of smtTerm
  | CheckSat
  | CheckSatAssuming of prop_literal list
  | DeclareConst of smtSymbol * smtSort
  | DeclareDatatype of smtSymbol * datatype_dec
  | DeclareDatatypes of smdSortDec list * datatype_dec list
  | DeclareFun of smtSymbol * smtSort list * smtSort
  | DeclareSmtSort of smtSymbol * numeral
  | DefineFun of func_def
  | DefineFunRec of func_def
  | DefineFunsRec of func_dec list * smtTerm list
  | DefineSmtSort of smtSymbol * smtSymbol list * smtSort
  | Echo of string
  | Exit
  | GetAssertions
  | GetAssignment
  | GetInfo of info_flag
  | GetModel
  | GetOption of string
  | GetProof
  | GetUnsatAssumptions
  | GetUnsatCore
  | GetValue of smtTerm list
  | Pop of numeral
  | Push of numeral
  | Reset
  | ResetAssertions
  | SetInfo of string
  | SetLogic of smtSymbol
  | SetOption of solver_option
  (* Z3 specific *)
  | Simplify of smtTerm * (solver_option list)

type script = command list



let pp_option (f : Formatter.t) (oname, ovalue : solver_option) =
  Fmt.(pf f ":%s %s" oname ovalue)

let pp_info_flag (f : Formatter.t) (i : info_flag) =
  match i with
  | 0 -> Fmt.(pf f ":all-statistics")
  | 1 -> Fmt.(pf f ":assertion-stack-levels")
  | 2 -> Fmt.(pf f ":authors")
  | 3 -> Fmt.(pf f ":error-behavior")
  | 4 -> Fmt.(pf f ":name")
  | 5 -> Fmt.(pf f ":reason-unknown")
  | 6 -> Fmt.(pf f ":version")
  | _ -> Fmt.(pf f "UNKNOWN_INFO_FLAG(%i)" i)


let pp_numeral (f : Formatter.t) (n : numeral) =
  Fmt.(pf f "%i" n)

let pp_smtSpecConstant (f : Formatter.t) (sc : smtSpecConstant) =
  match sc with
  | SCNumeral num -> pp_numeral f num

  | SCDecimal (n1, d, n2) ->
    Fmt.(pf f "%a.%a%a"
           pp_numeral n1
           (list ~sep:(fun _ _ -> ()) (fun f' _ -> Fmt.(pf f' "0")))
           (ListTools.init d (fun _ -> 0))
           pp_numeral n2)

  | SCHexaDecimal s -> Fmt.(pf f "#x%s" s)

  | SCBinary bl ->
    Fmt.(pf f "#b%a" (list ~sep:(fun _ _ -> ())
                        (fun f b -> if b then pf f "1" else pf f "0")) bl)

  | SCString s -> Fmt.(pf f "%s" s)

let pp_smtSymbol (f : Formatter.t) (s : smtSymbol) =
  match s with
  | SSimple x -> Fmt.(pf f "%s" x)
  | SQuoted x -> Fmt.(pf f "|%s|" x)

let pp_smtIndex (f : Formatter.t) (idx : smtIndex) =
  match idx with
  | INum n -> pp_numeral f n
  | ISym s -> pp_smtSymbol f s

let pp_smtIdentifier (f : Formatter.t) (id : smtIdentifier) =
  match id with
  | Id s -> pp_smtSymbol f s
  | IdC (s, ixl) ->
    Fmt.(pf f "(_ %a %a)" pp_smtSymbol s (list ~sep:sp pp_smtIndex) ixl)

let rec pp_sort (f : Formatter.t) (s : smtSort) =
  match s with
  | SmtSort x -> Fmt.pf f "%a" pp_smtIdentifier x
  | Comp (x, l) ->
    Fmt.(pf f "(%a %a)" pp_smtIdentifier x (list ~sep:sp pp_sort) l)

let pp_smtAttribute (f : Formatter.t) (attr : smtAttribute) =
  match attr with
  | ASymb anam -> Fmt.pf f "%s" anam
  | ASymbVal (aname, aval) -> Fmt.pf f "%s %s" aname aval

let pp_sortedVar (f : Formatter.t) (s, srt : smtSortedVar) =
  Fmt.pf f "(%a %a)" pp_smtSymbol s pp_sort srt

let pp_qual_ident (f : Formatter.t) (qi : smtQualIdentifier) =
  match qi with
  | QI s -> pp_smtIdentifier f s
  | QIas (s, smtSort) -> Fmt.pf f "(as %a %a)" pp_smtIdentifier s pp_sort smtSort

let pp_smtPattern (f : Formatter.t) (p : smtPattern) =
  match p with
  | Pat s -> pp_smtSymbol f s
  | PatComp (s, sl) -> Fmt.(pf f "(%a %a)" pp_smtSymbol s (list ~sep:sp pp_smtSymbol) sl)

let rec pp_smtTerm (f : Formatter.t) (t: smtTerm) =
  match t with
  | TSpecConst sc        -> Fmt.pf f "%a" pp_smtSpecConstant sc

  | TQualdId qi          -> Fmt.pf f "%a" pp_qual_ident qi

  | TApp (func, args)       ->
    Fmt.(pf f "(%a %a)" pp_qual_ident func (list ~sep:sp pp_smtTerm) args)

  | TLet (bindings, t')  ->
    Fmt.(pf f "(let (%a) %a)" (list ~sep:sp pp_binding) bindings pp_smtTerm t')

  | TForall (quants, t') ->
    Fmt.(pf f "(forall (%a) %a)" (list ~sep:sp pp_sortedVar) quants pp_smtTerm t')

  | TExists (quants, t') ->
    Fmt.(pf f "(exists (%a) %a)" (list ~sep:sp pp_sortedVar) quants pp_smtTerm t')

  | TMatch (t', cases)   ->
    Fmt.(pf f "(match %a (%a))" pp_smtTerm t' (list ~sep:sp pp_match_case) cases)

  | TAnnot (t', attrs)   ->
    Fmt.(pf f "(! %a %a)" pp_smtTerm t' (list ~sep:sp pp_smtAttribute) attrs)

and pp_binding (f : Formatter.t) (v, e : var_binding) =
  Fmt.pf f "(%a %a)" pp_smtSymbol v pp_smtTerm e

and pp_match_case (f : Formatter.t) (p, t : match_case) =
  Fmt.pf f "(%a %a)" pp_smtPattern p pp_smtTerm t



let pp_smtSelectorDec (f : Formatter.t) (s, srt : smtSelectorDec) =
  Fmt.pf f "(%a %a)" pp_smtSymbol s pp_sort srt

let pp_smtConstructorDec (f : Formatter.t) (s, sdecs : smtConstructorDec) =
  Fmt.(pf f "(%a %a)" pp_smtSymbol s (list ~sep:sp pp_smtSelectorDec) sdecs)

let pp_datatype_dec (f : Formatter.t) (dtdec : datatype_dec) =
  match dtdec with
  | DDConstr cd_list ->
    Fmt.(pf f "(%a)" (list ~sep:sp pp_smtConstructorDec) cd_list)

  | DDPar (symbs, cd_list) ->
    Fmt.((pf f "(par (%a) (%a))")
           (list ~sep:sp pp_smtSymbol) symbs
           (list ~sep:sp pp_smtConstructorDec) cd_list)

let pp_func_dec (f : Formatter.t) (s, svs, srt : func_dec) =
  Fmt.(pf f "(%a (%a) %a)" pp_smtSymbol s (list ~sep:sp pp_sortedVar) svs pp_sort srt)

let pp_func_def (f : Formatter.t) (s, svs, srt, t : func_def) =
  Fmt.(pf f "%a (%a) %a %a" pp_smtSymbol s (list ~sep:sp pp_sortedVar) svs pp_sort srt pp_smtTerm t)

let pp_prop_literal (f : Formatter.t) (pl : prop_literal) =
  match pl with
  | PL x -> Fmt.pf f "%a" pp_smtSymbol x
  | PLNot x -> Fmt.pf f "(not %a)" pp_smtSymbol x

let pp_smdSortDec (f : Formatter.t) (s, n : smdSortDec) =
  Fmt.pf f "(%a %a)" pp_smtSymbol s pp_numeral n

let pp_command (f : Formatter.t) (c : command) =
  match c with
  | Assert t -> Fmt.pf f "(assert %a)" pp_smtTerm t

  | CheckSat -> Fmt.pf f "(check-sat)"

  | CheckSatAssuming pl_list ->
    Fmt.(pf f "(check-sat-assuming (%a))" (list ~sep:sp pp_prop_literal) pl_list)

  | DeclareConst (sym, smtSort) ->
    Fmt.pf f "(declare-const %a %a)" pp_smtSymbol sym pp_sort smtSort

  | DeclareDatatype (sym, ddec) ->
    Fmt.(pf f "(declare-datatype %a %a)" pp_smtSymbol sym pp_datatype_dec ddec)

  | DeclareDatatypes (sdec_l, ddec_l) ->
    Fmt.(pf f "(declare-datatypes (%a) (%a))"
           (list ~sep:sp pp_smdSortDec) sdec_l
           (list ~sep:sp pp_datatype_dec) ddec_l)

  | DeclareFun (name, args, res)  ->
    Fmt.(pf f "(declare-fun %a (%a) %a)" pp_smtSymbol name (list ~sep:sp pp_sort) args pp_sort res)

  | DeclareSmtSort (s, n) ->
    Fmt.pf f "(declare-smtSort %a %a)" pp_smtSymbol s pp_numeral n

  | DefineFun fd -> Fmt.pf f "(define-fun %a)" pp_func_def fd

  | DefineFunRec fd -> Fmt.(pf f "(define-fun-rec %a)" pp_func_def fd)

  | DefineFunsRec (fdl, tl) ->
    Fmt.(pf f "(define-funs-rec (%a) (%a))"
           (list ~sep:sp pp_func_dec) fdl (list ~sep:sp pp_smtTerm) tl)

  | DefineSmtSort (s, sl, smtSort) ->
    Fmt.(pf f "(define-smtSort %a (%a) %a)" pp_smtSymbol s (list ~sep:sp pp_smtSymbol) sl pp_sort smtSort)

  | Echo s -> Fmt.pf f "(echo %s)" s

  | Exit -> Fmt.pf f "(exit)"

  | GetAssertions -> Fmt.pf f "(get-assertions)"

  | GetAssignment -> Fmt.pf f "(get-assignment)"

  | GetInfo iflag -> Fmt.pf f "(get-info %a)" pp_info_flag iflag

  | GetModel -> Fmt.pf f "(get-model)"

  | GetOption kw -> Fmt.pf f "(get-option %s)" kw

  | GetProof -> Fmt.pf f "(get-proof)"

  | GetUnsatAssumptions -> Fmt.pf f "(get-unsat-assumptions)"

  | GetUnsatCore -> Fmt.pf f "(get-unsat-core)"

  | GetValue tl -> Fmt.(pf f "(get-value %a)" (list ~sep:sp pp_smtTerm) tl)

  | Pop n -> Fmt.pf f "(pop %a)" pp_numeral n

  | Push n -> Fmt.pf f "(push %a)" pp_numeral n

  | Reset -> Fmt.pf f "(reset)"

  | ResetAssertions ->  Fmt.pf f "(reset-assertions)"

  | SetInfo attr -> Fmt.pf f "(set-info %s)" attr

  | SetLogic s ->  Fmt.pf f "(set-logic %a)" pp_smtSymbol s

  | SetOption o ->  Fmt.pf f "(set-option %a)" pp_option o

  (* Solver-specific commands *)

  | Simplify (t, ol) ->
    if List.is_empty ol then Fmt.pf f "(simplify %a)" pp_smtTerm t
    else Fmt.(pf f "(simplify %a %a)" pp_smtTerm t (list ~sep:sp pp_option) ol)


let write_command (out : OC.t) (c : command) : unit =
  let comm_s = Fmt.(to_to_string pp_command c) in
  OC.output_lines out [comm_s];
  OC.flush out

let pp_script (f : Formatter.t) (s : script) =
  List.iter ~f:(fun cm -> Fmt.pf f "%a@." pp_command cm) s


(* Term construction *)
(* SmtSymbol *)
let mk_symb s = SSimple s
(* Sorts *)
let mk_int_sort = SmtSort (Id (SSimple "Int"))
let mk_bool_sort = SmtSort (Id (SSimple "Bool"))
let mk_seq_sort t = Comp (Id (SSimple "Seq"), [t])
let mk_tuple_sort lt = Comp (Id (SSimple "Tuple"), lt)

(* Terms *)
let mk_qi s = QI(Id (SSimple s))
let mk_int (i : int) = TSpecConst (SCNumeral i)
let mk_false = TQualdId (QI (Id (SSimple "false")))
let mk_true = TQualdId (QI (Id (SSimple "true")))
let mk_nil  = TQualdId (QI (Id (SSimple "nil")))
let mk_simple_app (s : string) (args : smtTerm list) = TApp (QI (Id (SSimple s)), args)
let mk_var (s : string) = TQualdId (QI (Id (SSimple s)))

let mk_ite c e1 e2 = mk_simple_app "ite" [c;e1;e2]
let mk_add t1 t2 = mk_simple_app "+" [t1;t2]
let mk_sub t1 t2 = mk_simple_app "-" [t1;t2]
let mk_mul t1 t2 = mk_simple_app "*" [t1;t2]
let mk_div t1 t2 = mk_simple_app "/" [t1;t2]
let mk_and t1 t2 = mk_simple_app "and" [t1; t2]
let mk_or t1 t2 = mk_simple_app "or" [t1; t2]
let mk_eq t1 t2 = mk_simple_app "=" [t1;t2]
let mk_lt t1 t2 = mk_simple_app "<" [t1;t2]
let mk_gt t1 t2 = mk_simple_app ">" [t1;t2]
let mk_le t1 t2 = mk_simple_app "<=" [t1;t2]
let mk_ge t1 t2 = mk_simple_app ">=" [t1;t2]
let mk_not t1 = mk_simple_app "not" [t1]

(* Commands *)
let mk_assert (t : smtTerm) = Assert t
let mk_const_decl (s : string) (t : smtSort) = DeclareConst (SSimple s, t)
let mk_check_sat = CheckSat
let mk_fun_decl (s : string) (args : smtSort list) (res : smtSort)  =
  DeclareFun (SSimple s, args, res)
let mk_fun_def (s : string) (args : (string * smtSort) list) (res_sort : smtSort)  (body : smtTerm) =
  DefineFun (mk_symb s, List.map ~f:(fun (s, t) -> (mk_symb s, t)) args, res_sort, body)

let mk_named_assert (name : string) (t : smtTerm) = Assert (TAnnot (t, [ASymbVal(":named", name)]))
let mk_set_option (oname: string) (oval : string) = SetOption (oname, oval)
let mk_simplify ?(options : solver_option list = []) (t : smtTerm)  = Simplify (t, options)

let mk_print_success = SetOption ("print-success", "true")
let mk_exit = Exit
let mk_pop i = Pop i
let mk_push i = Push i

(* Specific function declarations *)
let mk_min_def =
  mk_fun_def "min" ["x",mk_int_sort;"y",mk_int_sort] mk_int_sort
    (mk_ite (mk_le (mk_var "x") (mk_var "y")) (mk_var "x") (mk_var "y"))

let mk_max_def =
  mk_fun_def "max" ["x",mk_int_sort;"y",mk_int_sort] mk_int_sort
    (mk_ite (mk_ge (mk_var "x") (mk_var "y")) (mk_var "x") (mk_var "y"))

(* SmtTerm / command helpers *)

let smtSymbol_of_decl (decl : command) =
  match decl with
  | DeclareConst (s, _) -> Some s
  | DeclareFun (s, _ ,_ ) -> Some s
  | DeclareDatatype (s, _) -> Some s
  | DeclareSmtSort (s, _ ) -> Some s
  | DefineFun (s, _, _, _) -> Some s
  | DefineFunRec (s, _, _, _) -> Some s
  | _ -> None


(* Given a list of commands, filter out the commands that are not declarations.
   Then, in the declaration, remove duplicates.
*)
let remove_duplicate_decls (s  : String.t Hash_set.t) (decls : command list) =
  let decls, nondecls =
    List.partition_tf ~f:(fun (s, _ ) -> is_some s)
      (List.map ~f:(fun comm -> (smtSymbol_of_decl comm, comm)) decls)
  in
  let uniq_decls =
    List.fold_left
      ~f:(fun uniq_decls (opt_name, decl) ->
          match opt_name with
          | Some name ->
            if List.Assoc.mem uniq_decls ~equal:symb_equal name ||
               Hash_set.mem s (str_of_symb name)
            then uniq_decls else (name,decl) :: uniq_decls
          | None -> uniq_decls)
      ~init:[] decls
  in
  (List.map ~f:snd uniq_decls) @  (List.map ~f:snd nondecls)


(* Reading solver responses *)
type solver_response =
  | Error of string
  | Sat
  | Unsat
  | Unknown
  | SExps of Sexp.t list [@sexp.list] [@@deriving_sexp]


type solver_kind =
  | Z3_SMT2 of int              (* Z3 smt2 soler with timeout *)
  | Z3_SMT2_Timeout_Fast        (* Z3 smt2 soler with fast timeout (1 sec) *)
  | CVC4_Default                (* CVC4 solver *)


(* Parse solver reponses *)
let parse_response (r : Sexp.t list) : solver_response =
  match r with
  | [Sexp.Atom "sat"]-> Sat
  | [Sexp.Atom "unsat"] -> Unsat
  | [Sexp.Atom "unkown"] -> Unknown
  | _ -> SExps r


let pp_solver_response f r =
  match r with
  | Sat ->       Fmt.pf f "sat"
  | Unsat ->     Fmt.pf f "unsat"
  | Unknown ->   Fmt.pf f "unkown"
  | SExps sl ->  Fmt.(pf f "%a" (list ~sep:sp Sexp.pp) sl)
  | Error s ->   Fmt.(pf f "(error %s)" s)
