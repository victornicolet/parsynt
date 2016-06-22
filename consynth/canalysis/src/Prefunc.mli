type preFunc = 
  | Empty
  | Container of Cil.exp
  | FBinop of Cil.binop * preFunc * preFunc
  | FUnop of Cil.unop * preFunc
  | ForLoop of preFunc * Loops.forIGU * Cil.exp list * preFunc
  | Guarded of preFunc * preFunc * preFunc

type guard =
    GEmpty 
  | GCond of Cil.exp * guard
  | GFor of Loops.forIGU * guard

val gcompose: guard -> guard -> guard
val build: ?subs:Cil.exp list -> guard -> Cil.exp -> Cil.varinfo -> preFunc
val replace: int -> preFunc -> preFunc -> preFunc
val string_of_prefunc: preFunc -> string
