open Cil
open Pretty
open List

module E = Errormsg
module S = Str

let v2e (v : varinfo): exp = Lval (var v)

let (|>) (a : 'a) (f: 'a -> 'b): 'b = f a

let map_2 (f : 'a -> 'b) ((a,b): ('a * 'a)) : ('b * 'b) = (f a, f b)

let map_3 (f : 'a -> 'b) ((a, b, c): ('a * 'a * 'a)) : ('b * 'b * 'b) = 
  (f a, f b, f c)

let checkOption (ao : 'a option) : 'a =
  match ao with
  | Some a -> a
  | None -> raise (Failure "checkOption")

let onlyFunc fn g =
  match g with
  | GFun (f, loc) -> fn f
  | _ -> ()

let onlyFuncLoc fn g =
  match g with
  | GFun (f, loc) -> fn f loc
  | _ -> ()

let appendC l a =
  List.append l 
    (if List.mem a l then [] else [a])

(** Cil specific utility functions *)
let setOfReachingDefs rdef =
  match rdef with
  | Some (_,_, setXhash) -> Some setXhash
  | None -> None
