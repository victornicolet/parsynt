open Cil
open List
open Printf
open Hashtbl
open Utils

module Errormsg = E

module Cloop = struct
  type t = {
  (** Each loop has a statement id in a Cil program *)
    sid: int;
    (** Loops can be nested. *)
    mutable parentLoops : int list;
  (** A loop appears in the body of a parent function declared globally *)
    mutable parentFunction : fundec;
  (** The set of function called in a loop body *)
    mutable calledFunctions : fundec list;
  (** The variables declared before entering the loop*)
    mutable definedInVars : varinfo list;
  (** The variables used after exiting the loop *)
    mutable usedOutVars : varinfo list;
  (** 
      Some variables too keep track of the state of the work done on the loop.
      - is the loop in normal form : the loop is in normal form when the outer 
      iterator is a stride-one integer.
      - is the loop body in SSA Form ?
      - does the loops contain break / continue / goto statements ?
  *)
    mutable inNormalForm : bool;
    mutable inSsaForm : bool;
    mutable hasBreaks : bool;
  }

  let create (sid : int) (parent : Cil.fundec) : t =
    { sid = sid;
      parentLoops = [];
      parentFunction = parent;
      calledFunctions = [];
      definedInVars = [];
      usedOutVars = [];
      inNormalForm = false;
      inSsaForm = false;
      hasBreaks = false; }

  let setParent l par =
    l.parentFunction <- par

  let getParent l =
    l.parentFunction


  (** Returns true if l1 contains the loop l2 *)
  let contains l1 l2 =
    let nested_in = List.mem l2.sid l1.parentLoops in
    let inlinable = List.mem l1.parentFunction l2.calledFunctions  in
    nested_in || inlinable
end


(** Each loop is stored according to the statement id *)
let programLoops = Hashtbl.create 10

let clearLoops () = 
  Hashtbl.clear programLoops

let addLoop (loop : Cloop.t) : unit =
  Hashtbl.add programLoops loop.Cloop.sid loop

let hasLoop (loop : Cloop.t) : bool =
  Hashtbl.mem programLoops loop.Cloop.sid


module LoopLocations = struct
  (** The statement ids of the loops in the program *)
  let loops : int list = []
  let loopMap = Hashtbl.create 
  (** Returns the list of functions in which for loops appear *)
  let functions (): fundec list =
    []
  (** Analyze a Cil file to identify where the loops are. *)
  let locateForLoops (cf : Cil.file) : unit = ()
end

class loopLocator topFunc = object (self)
  inherit Reachingdefs.rdVisitorClass
  method vstmt (s : stmt)  =
    match s.skind with
    | Loop _ ->
       addLoop (Cloop.create s.sid topFunc);
      
       DoChildren
    | Block _ | If _ | TryFinally _ | TryExcept _ ->
       DoChildren
    | Switch _ ->
       raise 
         (Failure ("Switch statement unexpected. "^
                      "Maybe you forgot to compute the CFG ?"))

    | _ -> SkipChildren
end      
      
let locateLoops fd : unit =
  Reachingdefs.computeRDs fd;
  let visitor = new loopLocator fd in
  ignore (visitCilFunction visitor fd)

    
let processFile cfile =
  iterGlobals cfile (onlyFunc locateLoops);
  
