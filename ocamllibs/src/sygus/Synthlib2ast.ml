open Format
open Utils.PpTools

(* Literals *)
type symbol = string

type syLiteral =
  | SyString of string
  | SyInt of int
  | SyReal of float
  | SyBool of bool
  | SyBitVector of string
  | SyEnum of symbol * symbol


type syLogic =
  | SyLIA
  | SyBV
  | SyReals
  | SyArrays

type sySort =
  | SyIntSort | SyBoolSort | SyRealSort
  | SyBitVecSort of int
  | SyArraySort of sySort * sySort
  | SyEnumSort of symbol list
  | SyIdSort of symbol

type syTerm =
  | SyApp of symbol * syTerm list
  | SyLiteral of syLiteral
  | SyId of symbol
  | SyLet of (symbol * sySort * syTerm) list * syTerm

type syGTerm =
  | SyGApp of symbol * syGTerm list
  | SyGLiteral of syLiteral
  | SyGId of symbol
  | SyGLet of (symbol * sySort * syGTerm) list * syGTerm
  | SyGConstant of sySort
  | SyGVariable of sySort
  | SyGInputVariable of sySort
  | SyGLocalVariable of sySort

type syNTDef = symbol * sySort * syGTerm list

type syCmd =
  | SySortDefCmd of symbol * sySort
  | SyVarDeclCmd of symbol * sySort
  | SyFunDeclCmd of symbol * sySort list * sySort
  | SyFunDefCmd of symbol * (symbol
                             * sySort) list * sySort * syTerm
  | SynthFunCmd of symbol * (symbol * sySort) list * sySort * syNTDef list
  | SyConstraintCmd of syTerm
  | SyCheckSynthCmd
  | SySetOptsCmd of (symbol * syLiteral) list

type sygusFile =
  | SyCommandsWithLogic of syLogic * (syCmd list)
  | SyCommands of syCmd list

let pp_space_sep_list printer=
  (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ")
     (fun fmt symb -> fprintf fmt "%a" printer symb))

let rec sypp_sort fmt (sort : sySort) =
  match sort with
  | SyIntSort -> fprintf fmt "Int"
  | SyBoolSort -> fprintf fmt "Bool"
  | SyRealSort -> fprintf fmt "Real"
  | SyBitVecSort i -> fprintf fmt "(BitVec %i)" i
  | SyEnumSort sl -> fprintf fmt "(Enum (%a))"
                       (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ")
                          (fun fmt symb -> fprintf fmt "%s" symb)) sl
  | SyArraySort (a, i) -> fprintf fmt "(Array %a %a)" sypp_sort a sypp_sort i
  | SyIdSort s -> fprintf fmt "%s" s


let sypp_arg fmt ((s, sort): symbol * sySort) =
  fprintf fmt "(%s %a)" s sypp_sort sort

let sypp_argslist fmt (argslist : (symbol * sySort) list) =
  (pp_space_sep_list sypp_arg) fmt argslist

let sypp_lit fmt (literal: syLiteral) =
  match literal with
  | SyString s -> fprintf fmt "\"%s\"" s
  | SyInt i -> fprintf fmt "%i" i
  | SyBool b -> fprintf fmt "%B" b
  | SyReal f -> fprintf fmt "%f" f
  | SyEnum (n, m) ->
    fprintf fmt "%s::%s" n m
  | SyBitVector v ->
    fprintf fmt "#b%s" v


let rec sypp_letlist fmt list =
  pp_space_sep_list
    (fun fmt (symb, sort, term) ->
       fprintf fmt "@[(%s %a@ %a)@]" symb sypp_sort sort sypp_term term)
    fmt list

and sypp_term fmt (term: syTerm) =
  match term with
  | SyApp (symb, args) ->
    fprintf fmt "@[(%s %a)@]" symb (pp_space_sep_list sypp_term) args
  | SyLiteral lit ->
    fprintf fmt "%a" sypp_lit lit
  | SyId id ->
    fprintf fmt "%s" id
  | SyLet (letlist, scope) ->
    fprintf fmt "@[<hov 2>(let (%a)@; %a)@]"
      sypp_letlist letlist sypp_term scope

let rec sypp_gletlist fmt list =
  pp_space_sep_list
    (fun fmt (symb, sort, term) ->
       fprintf fmt "@[(%s %a@ %a)@]" symb sypp_sort sort sypp_gterm term)
    fmt list

and sypp_gterm fmt (term: syGTerm) =
  match term with
  | SyGApp (symb, args) ->
    fprintf fmt "@[(%s %a)@]" symb (pp_space_sep_list sypp_gterm) args
  | SyGLiteral lit ->
    fprintf fmt "%a" sypp_lit lit
  | SyGId id ->
    fprintf fmt "%s" id
  | SyGLet (letlist, scope) ->
    fprintf fmt "@[<hov 2>(let (%a)@; %a)@]"
      sypp_gletlist letlist sypp_gterm scope
  | SyGConstant sort ->
    fprintf fmt "(Constant %a)" sypp_sort sort
  | SyGVariable sort ->
    fprintf fmt "(Variable %a)" sypp_sort sort
  | SyGInputVariable sort ->
    fprintf fmt "(InputVariable %a)" sypp_sort sort
  | SyGLocalVariable sort ->
    fprintf fmt "(LocalVariable %a)" sypp_sort sort


let sypp_ntdef fmt ((s, sort, gtlist): syNTDef) =
  fprintf fmt "@[<v 2>(%s %a (%a))@]"
    s sypp_sort sort (pp_space_sep_list sypp_gterm) gtlist

let sypp_command fmt (command : syCmd) =
  match command with
  | SySortDefCmd (symb, sort) ->
    fprintf fmt "@[<v 2>(define-sort %s@ %a)@]" symb sypp_sort sort
  | SyVarDeclCmd (symb, sort) ->
    fprintf fmt "@[<v 2>(declare-var %s %a)@]" symb sypp_sort sort
  | SyFunDeclCmd (symbol, sortlist, sort) ->
    fprintf fmt "@[<v 2>(declare-fun %s (%a) %a)@]" symbol
      (pp_space_sep_list sypp_sort) sortlist sypp_sort sort
  | SyFunDefCmd (symbol, argslist, sort, term) ->
    fprintf fmt "@[<v 2>(define-fun %s (%a)@ %a@ %a)@]"
      symbol sypp_argslist argslist sypp_sort sort sypp_term term
  | SynthFunCmd (symbol, argslist, sort, ntdef) ->
    fprintf fmt "@[<v 2>(synth-fun %s @[<v>(%a)@]@ %a@ (%a))@]"
      symbol sypp_argslist argslist sypp_sort sort
      (pp_space_sep_list sypp_ntdef) ntdef
  | SyConstraintCmd term ->
    fprintf fmt "@[<v 2>(constraint %a)@]" sypp_term term
  | SyCheckSynthCmd ->
    fprintf fmt "(check-synth)"
  | SySetOptsCmd slylist ->
    fprintf fmt "@[<v 2>(set-options @[(%a)@])@]"
      (pp_space_sep_list
         (fun fmt (s,ly) -> fprintf fmt "(%s %a)@;" s sypp_lit ly)) slylist

let sypp_commands fmt (commands : syCmd list) =
  pp_print_list
    ~pp_sep:(fun fmt () -> fprintf fmt "@.")
    (fun fmt cmd -> fprintf fmt "@[<v 2>%a@]" sypp_command cmd)
    fmt commands

let sypp_logic fmt (logic : syLogic) =
  let logicname =
    match logic with
    | SyLIA -> "LIA" | SyBV -> "BV" | SyReals -> "Reals" | SyArrays -> "Arrays"
  in
  fprintf fmt "(set-logic %s)" logicname

let sypp_sygus fmt (syfile : sygusFile) =
  match syfile with
  | SyCommandsWithLogic (logic, commands) ->
    fprintf fmt "%a@.%a@." sypp_logic logic sypp_commands commands
  | SyCommands commands ->
    fprintf fmt "%a@." sypp_commands commands


(* -------------------------------------------------------------------------- *)
let which_logic s =
  match s with
  | "LIA" -> SyLIA | "Arrays" -> SyArrays | "BV" -> SyBV | "Reals" -> SyReals
  (* Default Linear Integer Arithmetic *)
  | _ -> SyLIA


let rec replace ~id:id  ~by:t1 ~in_term:term =
  let _aux id' t1' t =  replace ~id:id' ~by:t1' ~in_term:t in
  match term with
  | SyApp (f, args) -> SyApp(f, List.map (_aux id t1) args)
  | SyLet (bindings, term0) ->
    SyLet(
      List.map (fun (vb, vs, ve) -> (vb, vs, _aux id t1 ve)) bindings,
      _aux id t1 term0)

  | SyId id' when id' = id -> t1
  | _ -> term
