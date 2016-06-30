open Cil
open Utils

(*
  Booleans
  boolean?, false?, true, false, not, nand, nor, implies, xor
  Integers and Reals
  number?, real?, integer?, zero?, positive?, negative?, even?, odd?,
  inexact->exact, exact->inexact, +, -, *, /, quotient, remainder
  , modulo, add1, sub1, abs, max, min, floor, ceiling, truncate,
  =, <, <=, >, >=, expt, pi, sgn
*)

type symbolicType =
  | Unit
  (** Base types : only booleans, integers and reals *)
  | Integer
  | Real
  | Boolean
  (** Type tuple *)
  | Tuple of symbolicType list
  (** Other lifted types *)
  | Bitvector of symbolicType * int
  (** A function in Rosette is an uniterpreted function *)
  | Function of symbolicType * symbolicType
  (** A procdedure is a reference to a procedure object *)
  | Procedure of symbolicType * symbolicType
  (** Pairs and lists *)
  | Pair of symbolicType
  | List of symbolicType * int option
  (** Vector and box *)
  | Vector of symbolicType * int option
  | Box of symbolicType
  (** User-defined structures *)
  | Struct of symbolicType

let string_of_baseSymbolicType =
  function
  | Integer -> "integer?"
  | Real -> "real?"
  | Boolean -> "boolean?"
  | _ -> failwith "not a symbolic type."

let rec symb_type_of_ciltyp =
  function
  | TInt (ik, _) ->
     begin
       match ik with
       | IBool -> Boolean
       | _ -> Integer
     end

  | TFloat _ -> Real

  | TArray (t, _, _) ->
     Vector (symb_type_of_ciltyp t, None)

  | TFun (t, arglisto, _, _) ->
     Procedure (symb_type_of_args arglisto, symb_type_of_ciltyp t)
  | TComp (ci, _) -> Unit
  | TVoid _ -> Unit
  | TPtr (t, _) ->
     Vector (symb_type_of_ciltyp t, None)
  | TNamed (ti, _) ->
     symb_type_of_ciltyp ti.ttype
  | TEnum _ | TBuiltin_va_list _ -> failwith "Not implemented"

and symb_type_of_args argslisto =
  try
    let argslist = checkOption argslisto in
    let symb_types_list =
      List.map
        (fun (s, t, atr) -> symb_type_of_ciltyp t)
        argslist
    in
    match symb_types_list with
    | [] -> Unit
    | [st] -> st
    | _ -> Tuple symb_types_list
  with Failure s -> Unit
