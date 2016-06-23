module VS = Utils.VS

type preFunc =
  | Empty of Cil.varinfo
  | Func of Cil.varinfo * lambda
and lambda = 
  | Exp of fexp
  | Let of int * fexp * lambda
and fexp =
  | Id of int
  | Container of Cil.exp
  | Binop of Cil.binop * fexp * fexp
  | Unop of Cil.unop * fexp
  | Loop of Loops.forIGU * Cil.exp list * fexp
  | Cond of fexp * fexp * fexp

type guard =
    GEmpty 
  | GCond of Cil.exp * guard
  | GFor of Loops.forIGU * guard

val gcompose: guard -> guard -> guard
val build: ?subs:Cil.exp list -> guard -> Cil.exp -> Cil.varinfo -> 
  int list -> fexp
val replace: int -> fexp -> fexp -> fexp
val letin: Cil.varinfo -> lambda -> fexp -> lambda
val let_in_func: Cil.varinfo -> preFunc -> fexp -> preFunc
val vs_of_prefunc: VS.t -> preFunc -> VS.t
val vs_of_lam: VS.t -> lambda -> VS.t
val vs_of_fexp: VS.t -> fexp -> VS.t

val string_of_prefunc: preFunc -> string
val string_of_lambda: lambda -> string
val string_of_fexp: fexp -> string
