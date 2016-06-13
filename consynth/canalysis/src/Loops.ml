open Cil
open List
open Printf
open Hashtbl
open Utils
open Map

module Errormsg = E
module Pf = Map.Make(String)

module Cloop = struct
  type t = {
  (** Each loop has a statement id in a Cil program *)
    sid: int;
    (** Loops can be nested. *)
    mutable parentLoops : int list;
  (** A loop appears in the body of a parent function declared globally *)
    mutable parentFunction : varinfo;
  (** The set of function called in a loop body *)
    mutable calledFunctions : varinfo list;
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

  let create (sid : int) (parent : Cil.varinfo) : t =
    { sid = sid;
      parentLoops = [];
      parentFunction = parent;
      calledFunctions = [];
      definedInVars = [];
      usedOutVars = [];
      inNormalForm = false;
      inSsaForm = false;
      hasBreaks = false; }
      
  let id l = l.sid

  let setParent l par =
    l.parentFunction <- par

  let getParent l =
    l.parentFunction

  (** 
      Append a parent loop to the list of parent loops.
      The AST is visited top-down, so the list should contains
      parent loops for outermost to innermost.
  *)
  let addParentLoop l  parentSid =
    l.parentLoops <- Utils.appendC l.parentLoops parentSid

  let addCalledFunc l vi =
    l.calledFunctions <- Utils.appendC l.calledFunctions vi

  (** The loops contains either a break, a continue or a goto statement *)
  let setBreak l =
    l.hasBreaks <- true

  (** Returns true if l1 contains the loop l2 *)
  let contains l1 l2 =
    let nested_in = List.mem l2.sid l1.parentLoops in
    let inlinable = List.mem l1.parentFunction l2.calledFunctions  in
    nested_in || inlinable
end


(** Each loop is stored according to the statement id *)
let programLoops = Hashtbl.create 10
let programFuncs = ref Pf.empty

let clearLoops () = 
  Hashtbl.clear programLoops

let addLoop (loop : Cloop.t) : unit =
  Hashtbl.add programLoops loop.Cloop.sid loop

let hasLoop (loop : Cloop.t) : bool =
  Hashtbl.mem programLoops loop.Cloop.sid

let addGlobalFunc (fd : Cil.fundec) =
  programFuncs := Pf.add fd.svar.vname fd !programFuncs



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


(** Loop locations inspector. During a first visit of the control flow
    graph, we store the loop locations, with the containing functions*)
class loopLocator topFunc = object
  inherit nopCilVisitor
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
end ;;


(** The loop inspector inspects the body of the loop tl and adds information
    about :
    - loop nests
    - functions used
    - presence of break/gotos statements in cf *)
class loopInspector (tl : Cloop.t) = object
  inherit nopCilVisitor

  method vstmt (s : Cil.stmt) =
    match s.skind with
    | Loop _ ->
       (** The inspected loop is nested in the current loop *)
       Cloop.addParentLoop (Hashtbl.find programLoops s.sid) (Cloop.id tl) ;
      DoChildren
    | Block _ | If _ | TryFinally _ | TryExcept _ -> DoChildren
    | Switch _ -> 
       raise 
         (Failure ("Switch statement unexpected. "^
          "Maybe you forgot to compute the CFG ?"))
    (**
       If the loop has a control-flow breaking statement, we mark the loop as 
       such but stop visiting children. Currently, we do not support breaks
       and the loops will not be parallelized.
    *)
    | Goto _ | ComputedGoto _ | Break _ | Continue _ | Return _->
       Cloop.setBreak tl;
      SkipChildren
    | Instr _ ->
       DoChildren
        
  method vinstr (i : Cil.instr) : Cil.instr Cil.visitAction =
    match i with
    | Call (lval_opt, ef, elist, _)  -> 
         SkipChildren
    | _ -> () ; 
      SkipChildren

end

let locateLoops fd : unit =
  Reachingdefs.computeRDs fd;
  addGlobalFunc fd;
  let visitor = new loopLocator fd.svar in
  ignore (visitCilFunction visitor fd)

    
let processFile cfile =
  iterGlobals cfile (Utils.onlyFunc locateLoops);
  
