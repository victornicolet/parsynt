open Cil
open Printf
open LoopsHelper
open Utils

module E = Errormsg
module IH = Inthash
module Pf = Map.Make(String)
module VS = Utils.VS
module LF = Liveness.LiveFlow
module EC = Expcompare

let verbose = ref true
let debug = ref false

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
let get_loop_condition b =
  (* returns the first non-empty
   * statement of a statement list *)
  (* stm list -> stm list *)
  let rec skipEmpty = function
    | [] -> []
    | {skind = Instr []; labels = []}::rest ->
	   skipEmpty rest
    | x -> x
  in
  (* stm -> exp option * instr list *)
  let rec get_cond_from_if if_stm =
    match if_stm.skind with
      If(e,tb,fb,_) ->
	    let e = EC.stripNopCasts e in
	    let tsl = skipEmpty tb.bstmts in
	    let fsl = skipEmpty fb.bstmts in
	    (match tsl, fsl with
	      {skind = Break _} :: _, [] -> Some e
	    | [], {skind = Break _} :: _ ->
	       Some(UnOp(LNot, e, intType))
	    | ({skind = If(_,_,_,_)} as s) :: _, [] ->
	       let teo = get_cond_from_if s in
	       (match teo with
	         None -> None
	       | Some te ->
		      Some(BinOp(LAnd,e,EC.stripNopCasts te,intType)))
	    | [], ({skind = If(_,_,_,_)} as s) :: _ ->
	       let feo = get_cond_from_if s in
	       (match feo with
	         None -> None
	       | Some fe ->
		      Some(BinOp(LAnd,UnOp(LNot,e,intType),
			             EC.stripNopCasts fe,intType)))
	    | {skind = Break _} :: _, ({skind = If(_,_,_,_)} as s):: _ ->
	       let feo = get_cond_from_if s in
	       (match feo with
	         None -> None
	       | Some fe ->
		      Some(BinOp(LOr,e,EC.stripNopCasts fe,intType)))
	    | ({skind = If(_,_,_,_)} as s) :: _, {skind = Break _} :: _ ->
	       let teo = get_cond_from_if s in
	       (match teo with
	         None -> None
	       | Some te ->
		      Some(BinOp(LOr,UnOp(LNot,e,intType),
			             EC.stripNopCasts te,intType)))
	    | ({skind = If(_,_,_,_)} as ts) :: _ ,
           ({skind = If(_,_,_,_)} as fs) :: _ ->
	       let teo = get_cond_from_if ts in
	       let feo = get_cond_from_if fs in
	       (match teo, feo with
	         Some te, Some fe ->
		       Some(BinOp(LOr,BinOp(LAnd,e,EC.stripNopCasts te,intType),
			              BinOp(LAnd,UnOp(LNot,e,intType),
				                EC.stripNopCasts fe,intType),intType))
	       | _,_ -> None)
	    | _, _ -> (if !debug
          then ignore(E.log "cond_finder: branches of %a not good\n"
					                       d_stmt if_stm);
		           None))
    | _ -> (if !debug
      then ignore(E.log "cond_finder: %a not an if\n" d_stmt if_stm);
	        None)
  in
  let sl = skipEmpty b.bstmts in
  match sl with
    ({skind = If(_,_,_,_); labels=[]} as s) :: rest ->
      get_cond_from_if s, rest
  | s :: _ ->
     (if !debug then ignore(E.log "checkMover: %a is first, not an if\n"
			                  d_stmt s);
      None, sl)
  | [] ->
     (if !debug then ignore(E.log "checkMover: no statements in loop block?\n");
      None, sl)


(** Get the initiatlization, termination and update in a*)
let get_loop_IGU loop_stmt : (forIGU option * Cil.stmt list) =
  match loop_stmt.skind with
  | Loop (bdy, _, _, _) ->
     begin
       try
         let body_copy = Cil.mkBlock bdy.bstmts in
         let term_expr_o, rem = get_loop_condition body_copy in
         let term_expr = match term_expr_o with
           | Some expr ->
              expr
           | None ->
              raise (Failure "couldn't get the term condition.")
         in
         let init = lastInstr (List.nth loop_stmt.preds 1) in
         let update, newbody =
           match  remLastInstr rem with
           | Some instr, Some s ->
              instr, s
           | None, Some s ->
              begin
                ppbk (Cil.mkBlock s);
                raise (Failure "failed to find last intruction.")
              end
           | Some _, None
           | None, None ->
              raise (Failure "failed to find last statement in body.")
         in
         Some (init, (neg_exp term_expr), update), newbody
       with Failure s ->
		 print_endline ("get_loop_IGU : "^s); None , bdy.bstmts
     end
  |_ ->
     raise(
       Failure(
         "get_loop_IGU : bad argument, expected a Loop statement."))

(**
    Checking that the triplet is well-formed. The initialisation and update
    must update the same variable. The restrict the termination condition too,
    it has to refer to the loop index i.
*)

let indexOfIGU ((init, guard, update) : forIGU) : VS.t =
  VS.inter
    (VS.inter (VSOps.sovi init) (VSOps.sove guard))
    (VSOps.sovi update)

let checkIGU ((init, guard, update) : forIGU) : bool =
  let i = indexOfIGU (init, guard, update) in
  (VS.cardinal i) = 1


let sprint_IGU ((init, guard, update) : forIGU) : string =
  sprintf "for(%s; %s; %s)"
    (psprint80 Cil.d_instr init)
    (psprint80 Cil.d_exp guard)
    (psprint80 Cil.d_instr update)

module Cloop = struct
  type t = {
  (** Each loop has a statement id in a Cil program *)
    sid: int;
    mutable loopStatement : Cil.stmt;
    (** Modified body of the loop *)
    mutable statements : Cil.stmt list;
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
    mutable rwset : int list * int list * int list;
  (**
      Some variables too keep track of the state of the work done on the loop.
      - is the loop in normal form : the loop is in normal form when the outer
      iterator is a stride-one integer.
      - is the loop body in SSA Form ?
      - does the loops contain break / continue / goto statements ?
  *)
    mutable hasBreaks : bool;
  }

  let create (lstm : Cil.stmt)
      (parent : Cil.varinfo) (f : Cil.file) : t =
    { sid = lstm.sid;
      loopStatement = lstm;
      statements = [];
      loopIGU = None;
      parentFile = f;
      parentLoops = [];
      parentFunction = parent;
      calledFunctions = [];
      definedInVars = IH.create 32;
      usedOutVars = [];
      rwset = ([], [], []);
      hasBreaks = false;
    }

  let id l = l.sid

  (** Parent function *)

  let setParent l par = l.parentFunction <- par

  let getParent l = l.parentFunction

  let getParentFundec l =
    checkOption
      (getFn l.parentFile l.parentFunction.vname)

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


  (**
     Setting the defined-In variables il also needed to access variable
     information in further steps. If a varaible is not "defined in" then
     we cannot access it, considering also the fact that the Cil representation
     puts all the local variable declarations in the function body at the top
     of the function, so we don't have any local variable declaration in the
     loop body.
  *)
  let setDefinedInVars l vid2did vs =
    let vid2v = hashVS vs in
    addHash l.definedInVars vid2v vid2did

  let getDefinedInVars l = l.definedInVars

  (**
     Once the defined vars are set we can have variable information directly
     from within the Cloop module.
  *)

  let getVarinfo l vid  =
    try
      match IH.find l.definedInVars vid with
      | (vi, _) -> vi
    with
      Not_found ->
        begin
          if IH.length l.definedInVars < 1
          then
            raise
              (Failure
                 "The definedInVars are empty. Perhaps you
forgot initializing them ?")
          else
            raise
              (Failure
                 (Printf.sprintf
                    "Failed in getVarinfo. The variable with id %i
is not defined at the beginning of the loop"
                    vid))
        end
  (**
     Set read/write set ifnormation. The set of defined-in variables should
     be comnputed before in order to associate variable IDs with variable
     names.
  *)
  let setRW l (uses, defs) ?(checkDefinedIn = false) =
	let r = List.map (fun v -> v.vid) (VS.elements uses) in
	let w = List.map (fun v -> v.vid) (VS.elements defs) in
	let rw = List.map (fun v -> v.vid)
	  (VS.elements (VS.inter uses defs)) in
	l.rwset <- (r, w, rw)


  let string_of_rwset (cl : t) =
    let (r, w, rw) = cl.rwset in
    let transform l = String.concat " "
      (List.map (fun k ->
		try
		  (getVarinfo cl k).vname
	  with Failure s -> "*")l)
	in
    let (rs, ws, rws) = (transform r, transform w, transform rw) in
    "Read set : "^rs^"\nWrite set : "^ws^"\nRead-Write set:"^rws^"\n"
  (**
      Append a parent loop to the list of parent loops.
      The AST is visited top-down, so the list should contains
      parent loops for outermost to innermost.
  *)
  let addParentLoop l  parentSid =
    l.parentLoops <- appendC l.parentLoops parentSid

  let addCalledFunc l vi =
    l.calledFunctions <- appendC l.calledFunctions vi

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
      then "\n"^(sprint_IGU (checkOption cl.loopIGU))
      else ""
    in
    let rwsets = string_of_rwset cl in
    sprintf "---> Loop %s in %s:\nCalls: %s\n%s%s\n%s"
      sid pfun cfuns defvarS oigu rwsets
end

(******************************************************************************)
(** Each loop is stored according to the statement id *)
let fileName = ref ""
let programLoops = IH.create 10
let programFuncs = ref Pf.empty

let clearLoops () =
  IH.clear programLoops

let addLoop (loop : Cloop.t) : unit =
  IH.add programLoops loop.Cloop.sid loop

let hasLoop (loop : Cloop.t) : bool =
  IH.mem programLoops loop.Cloop.sid

let getFuncWithLoops () : Cil.fundec list =
  IH.fold
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

let getGlobalFuncVS () =
  VS.of_list
	(List.map (fun (a,b) -> b)
	   (Pf.bindings (Pf.map (fun fd -> fd.svar) !programFuncs)))



(******************************************************************************)
(** LOCATIONS *)

(**
    Loop locations inspector. During a first visit of the control flow
    graph, we store the loop locations, with the containing functions
*)

class loopLocator (topFunc : Cil.varinfo) (f : Cil.file) = object
  inherit nopCilVisitor
  method vstmt (s : stmt)  =
    match s.skind with
    | Loop (b, loc, o1, o2) ->
       let cloop = (Cloop.create s topFunc f) in
       let igu, stmts = get_loop_IGU s in
       begin
         match igu with
         | Some figu ->
            if checkIGU figu then
              begin
                cloop.Cloop.loopIGU <- Some figu;
                cloop.Cloop.statements <- stmts;
              end
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
(** INNER BODY INSPECTION *)

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
       Cloop.addParentLoop (IH.find programLoops s.sid) (Cloop.id tl) ;
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
   the reaching definitions (variables defined in) and the set of variables that
   are used after the loop
*)

let addBoundaryInfo clp =
  let sid = clp.Cloop.sid in
  let rds =
    match (setOfReachingDefs
             (Reachingdefs.getRDs sid))
    with
    | Some x -> x
    | None ->
       if !debug || true then
         begin
           Printf.eprintf
             "addBoundaryInfo - no reaching defs in (sid : %i):\n %s\n"
             sid
             (psprint80 d_stmt clp.Cloop.loopStatement)
         end;
      IH.create 2
  in
  let livevars =
	try IH.find LF.stmtStartData sid
	with Not_found -> (raise (Failure "addBoundaryInfo : live variables \
 statement data not found "))
  in
  let stmt =
    if VS.cardinal livevars = 0
    then
      begin
        if !debug || true then
          begin
            Printf.eprintf
              "addBoundaryInfo - no live variables in (sid : %i):\n %s\n"
              sid
              (psprint80 d_stmt clp.Cloop.loopStatement);

          end;
        raise (Failure "addBoundaryInfo : no live variables.");
      end
    else
      begin
        Cloop.setDefinedInVars clp rds livevars;
      (** Visit the loop statement and compute some information *)
        visitCilStmt (new loopInspector clp) clp.Cloop.loopStatement
      end
  in
  clp.Cloop.loopStatement <- stmt


(******************************************************************************)
(** Read/write set *)
(**
    Custom dataflow analysis not provided by Cil.
    Main components :
    - Read/Write set of a body
*)
(** Here we do not use Cil's Dataflow framework *)

module RW = struct

  let verbose = ref false

  let prws u d =
	print_endline "--Uses";
	VS.iter ppv u;
	print_endline "Defs";
	VS.iter ppv d

  let computeRWs (loop : Cil.stmt) (fnames : VS.t) : VS.t * VS.t  =
	Usedef.onlyNoOffsetsAreDefs := true;
	let _u, _d = Usedef.computeDeepUseDefStmtKind loop.skind in
	let u, d = VS.diff _u fnames, VS.diff _d fnames in
	if !verbose then prws u d;
	u, d
end

let addRWinformation sid clp =
  RW.verbose := !verbose;
  let stmts =
    match clp.Cloop.loopStatement.skind with
    | Loop (blk,_, _, _) -> blk.bstmts
    | _ -> raise (Failure "Expected a loop statement") in
  if !verbose
  then
    begin
      print_string "AddRW information :";
	  print_endline (psprint80 Cil.d_stmt (last stmts))
    end
  else ();
  let rwinfo =  RW.computeRWs clp.Cloop.loopStatement (getGlobalFuncVS ()) in
  Cloop.setRW clp rwinfo ~checkDefinedIn:false

(******************************************************************************)
(** Exported functions *)
(**
    Main entry point. Do not simplify in three-address code here, or it will
    break the for-loop recgnition which is only based on the CFG structure.

    Returns the vids of the processed functions.
*)

let processFile cfile =
  fileName := cfile.fileName;
  (** Locate the loops in the file *)
  iterGlobals cfile (onlyFunc (fun fd -> locateLoops fd cfile));
  (**
	 Visit each function containing a loop, but compute cil information
	 like Reaching defintions and live variables each time the function
	 is visited.
  *)
  let visited_funcs =
    IH.fold
      (fun k cl visited_fids ->
        let fdc = Cloop.getParentFundec cl in
        let vis_fids =
          if List.mem fdc.svar.vid visited_fids
		  then visited_fids
          else
            begin
              visited_fids@[fdc.svar.vid]
            end
        in
        Reachingdefs.computeRDs fdc;
        Liveness.computeLiveness fdc;
        addBoundaryInfo cl;
        addRWinformation k cl;
        vis_fids)
      programLoops []
  in
  (**
      Remove the loops with missing information and
      the loops containing break statements.
  *)
  let rem_cond cl =
    cl.Cloop.hasBreaks ||
      ((IH.length cl.Cloop.definedInVars) = 0)
  in
  let loops_to_remove =
    IH.fold
      (fun k cl lp_brks ->
        if rem_cond cl then
          k::lp_brks
        else lp_brks
      )
      programLoops
      []
  in
  List.iter
    (fun sid -> IH.remove programLoops sid)
    loops_to_remove;
  visited_funcs

(**
    Return the set of processed loops. To check if a program has been
    processed, we check if the fileName has been assigned.
    A program could be totally loop free !
*)

let processedLoops () =
  if (!fileName = "") then
    raise (Failure "No file processed, no loop data !")
  else
    programLoops

let clear () =
  fileName := "";
  clearLoops ();
  programFuncs := Pf.empty
