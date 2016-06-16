open Cil
open Cflows
open Printf

module E = Errormsg
module IH = Inthash
module Pf = Map.Make(String)
module VS = Utils.VS
module LF = Liveness.LiveFlow
(** 
    The integer option set used in Cil implementation of reachingdefs.ml.
    A set of "int option". 
*)
module IOS = Reachingdefs.IOS
(** 
    Map of Cil reaching definitions, maps each variable id 
    to a set of definition ids that reach the statement.
*)
type defsMap = (VS.elt * (IOS.t option))  IH.t


(** 
    The for loop statement can be strored as a triplet of 
    initialization instruction, guard condition and update instructions
*)
type forIGU = (Cil.instr * Cil.exp * Cil.instr)

(** Extracting the termination condition of the loop *)
let match_for_loop loop_stmt : forIGU option =
  match loop_stmt.skind with
  | Loop _ ->
     begin
       try
         let if_brk = List.hd loop_stmt.succs in (** Not always working TDOD :
                                                     better identification of
                                                     termination cond.*)
         let term_expr =
           match if_brk.skind with
           | If (e, b1, b2, _) -> e;
           (* e is the termination expr. in the for loop *)
           | _ -> raise (Failure "Unexpected loop stmt sucessor.")
         in
         let init = Utils.lastInstr (List.nth loop_stmt.preds 1) in
         let update = Utils.lastInstr (List.nth loop_stmt.preds 0) in
         Some (init, term_expr, update)
       with Failure s -> print_endline s;  None
     end
  |_ -> print_endline "failed match_for_loop"; None

(** 
    Checking the weel formedness of the triplet. The initialisation and update
    must update the same variable. The restrict the termination condition too,
    it has to refer to the loop index i.
*)

let check_loop ((init, guard, update) : forIGU) : bool =
  let i = VS.inter
    (VS.inter (Utils.sovi init) (Utils.sove guard))
    (Utils.sovi update) in
  (VS.cardinal i) = 1


let sprint_IGU ((init, guard, update) : forIGU) : string = 
  sprintf "for(%s; %s; %s)"
    (Pretty.sprint 80 (Cil.d_instr () init))
    (Pretty.sprint 80 (Cil.d_exp () guard))
    (Pretty.sprint 80 (Cil.d_instr () update))

module Cloop = struct
  type t = {
  (** Each loop has a statement id in a Cil program *)
    sid: int;
    (** If it is a for loop the init-guard-update can be summarized*)
    mutable loopIGU : forIGU option;
    (** The file in which the loop appears *)
    mutable parentFile: Cil.file;
    (** Loops can be nested. *)
    mutable parentLoops : int list;
  (** A loop appears in the body of a parent function declared globally *)
    mutable parentFunction : varinfo;
  (** The set of function called in a loop body *)
    mutable calledFunctions : varinfo list;
  (** The variables declared before entering the loop*)
    mutable definedInVars : defsMap;
  (** The variables used after exiting the loop *)
    mutable usedOutVars : varinfo list;
    (** A map of variable ids to integers, to determine if the variable is in
    the read or write set*)
    mutable rwset : Utils.IS.t;
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

  let create (sid : int) (parent : Cil.varinfo) (f : Cil.file) : t =    
    { sid = sid;
      loopIGU = None;
      parentFile = f;
      parentLoops = [];
      parentFunction = parent;
      calledFunctions = [];
      definedInVars = IH.create 32;
      usedOutVars = [];
      rwset = Utils.IS.empty;
      inNormalForm = false;
      inSsaForm = false;
      hasBreaks = false; }
      
  let id l = l.sid

  (** Parent function *)

  let setParent l par = l.parentFunction <- par

  let getParent l = l.parentFunction

  let getParentFundec l =
    Utils.checkOption 
      (Utils.getFn l.parentFile l.parentFunction.vname)

  (** Defined variables at the loop statement*)
  let string_of_defvars l = 
    let setname = "Variables defined at the entry of the loop:\n{" in
    let str = IH.fold
      (fun k (vi, dio) s -> let vS = s^" "^vi.vname in
                            match dio with
                            | Some mapping -> vS^"[defs]"
                            | None -> vS) 
      l.definedInVars setname in
    str^"}"

  let setDefinedInVars l vid2did vs = 
    let vid2v = Utils.hashVS vs in
    Utils.addHash l.definedInVars vid2v vid2did

  let getDefinedInVars l = l.definedInVars

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

  let isForLoop l = match l.loopIGU with Some s -> true | None -> false 

  let string_of_cloop (cl : t) =
    let sid = string_of_int cl.sid in
    let pfun = cl.parentFunction.vname in
    let cfuns = String.concat ", " 
      (List.map (fun y -> y.vname) cl.calledFunctions) in
    let defvarS = string_of_defvars cl in
    let oigu = if isForLoop cl 
      then "\n"^(sprint_IGU (Utils.checkOption cl.loopIGU))
      else "" 
    in
    sprintf "Loop %s in %s:\nCalls: %s\n%s%s\n" sid pfun cfuns defvarS oigu
end

(******************************************************************************)
(** Each loop is stored according to the statement id *)
let fileName = ref ""
let programLoops = Hashtbl.create 10
let programFuncs = ref Pf.empty

let clearLoops () =
  Hashtbl.clear programLoops

let addLoop (loop : Cloop.t) : unit =
  Hashtbl.add programLoops loop.Cloop.sid loop

let hasLoop (loop : Cloop.t) : bool =
  Hashtbl.mem programLoops loop.Cloop.sid

let getFuncWithLoops () : Cil.fundec list =
  Hashtbl.fold
    (fun k v l ->
      let f = 
        try
          Pf.find v.Cloop.parentFunction.vname !programFuncs 
        with Not_found -> raise (Failure "x")
      in
      f::l)
    programLoops []

let addGlobalFunc (fd : Cil.fundec) =
  programFuncs := Pf.add fd.svar.vname fd !programFuncs



(******************************************************************************)

(** Loop locations inspector. During a first visit of the control flow
    graph, we store the loop locations, with the containing functions*)

class loopLocator topFunc f = object
  inherit nopCilVisitor
  method vstmt (s : stmt)  =
    match s.skind with
    | Loop _ ->
       let cloop = (Cloop.create s.sid topFunc f) in
       let igu = match_for_loop s in
       begin
         match igu with
         | Some figu ->
            if check_loop figu then 
              cloop.Cloop.loopIGU <- Some figu
            else ()
         | _ -> ()
       end;
         addLoop cloop;
      DoChildren
    | Block _ | If _ | TryFinally _ | TryExcept _ ->
       DoChildren
    | Switch _ ->
       raise 
         (Failure ("Switch statement unexpected. "^
                      "Maybe you forgot to compute the CFG ?"))

    | _ -> SkipChildren
end ;;



let locateLoops fd f : unit =
  addGlobalFunc fd;
  let visitor = new loopLocator fd.svar f in
  ignore (visitCilFunction visitor fd)


(******************************************************************************)

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
        
  method vinst (i : Cil.instr) : Cil.instr list Cil.visitAction =
    match i with
    | Call (lval_opt, ef, elist, _)  -> 
       begin
         match ef with
         | Lval (Var vi, _) -> Cloop.addCalledFunc tl vi
         | _ -> ()
       end;
      SkipChildren
    | _ -> SkipChildren
end

(******************************************************************************)

(**
   Now for each loop we process the function containing the loop and compute
   the reaching definitons (variables defined in) and the set of variables that
   are used after the loop
*)

class defsVisitor = object (self)
  inherit nopCilVisitor 

  method vstmt (s : Cil.stmt) =
    begin
      if Hashtbl.mem programLoops s.sid 
      then 
        let clp = Hashtbl.find programLoops s.sid in
        let rds = 
          match (Utils.setOfReachingDefs 
                   (Reachingdefs.getRDs s.sid)) with
          | Some x -> x
          | None -> printf "bad"; IH.create 2
        in
        (printf "%d\n" (IH.length rds));
        let livevars = IH.find LF.stmtStartData s.sid in
        Cloop.setDefinedInVars clp rds livevars;
        ignore(visitCilStmt (new loopInspector clp) s)
    end;
    DoChildren
end

let visitPfunc pgm clp =
  let fdc = Cloop.getParentFundec clp in
  Reachingdefs.computeRDs fdc;
  Liveness.computeLiveness fdc;
  let visitor = new defsVisitor in
  ignore(Cil.visitCilFunction visitor fdc)


(******************************************************************************)
(** Exported functions *)

let processFile cfile =
  fileName := cfile.fileName;
  iterGlobals cfile Simplify.doGlobal;
  iterGlobals cfile (Utils.onlyFunc (fun fd -> locateLoops fd cfile));
  Hashtbl.iter (fun k v -> visitPfunc cfile v) programLoops

(** 
    Return the set of processed loops. To check if a program has been
    processed, we check if the fileName has been assigned. 
    A program could be totally loop free !
*)
let processedLoops () =
  if (!fileName = "") then
    raise (Failure "No file processed, no looop data !")
  else
    programLoops

let clear () =
  fileName := "";
  clearLoops ();
  programFuncs := Pf.empty
