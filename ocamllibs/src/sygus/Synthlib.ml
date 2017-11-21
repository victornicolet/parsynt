open Format
open Synthlib2ast
open Sylexer

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
