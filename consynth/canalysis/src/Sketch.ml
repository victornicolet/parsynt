open Utils
open Loops

type skLet =
  | skLetExpr of skExpr
  | skLetIn of int * skExpr * skLet

and skExpr =
  | skId of int
  | skCil of exp
  | skBinop of binop * skExpr * skExpr
  | skUnop of unop * skExpr
  | skRec of  forIGU * skExpr
  | skCond of skExpr * skExpr * skExpr
  | skHole of int list

and skStmt =  varinfo * skLet

type sketch = skStmt list
