open Cil
open Format
open LoopsHelper
open Utils
open Utils.ListTools
open PpHelper
open VariableAnalysis

module E = Errormsg
module SM = Map.Make(String)
module VS = Utils.VS
module LF = Liveness.LiveFlow
module Ct = CilTools


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
type forIGU = LoopsHelper.forIGU

(**
    Checking that the triplet is well-formed. The initialisation and update
    must update the same variable. The restrict the termination condition too,
    it has to refer to the loop index i.
*)

let index_of_igu ((init, guard, update) : forIGU) : VS.t =
  VS.inter
    (VS.inter (VSOps.sovi init) (VSOps.sove guard))
    (VSOps.sovi update)

let check_igu ((init, guard, update) : forIGU) : bool =
  let i = index_of_igu (init, guard, update) in
  (VS.cardinal i) = 1


let sprint_igu ((init, guard, update) : forIGU) : string =
  sprintf "for(%s; %s; %s)"
    (Ct.psprint80 Cil.d_instr init)
    (Ct.psprint80 Cil.d_exp guard)
    (Ct.psprint80 Cil.d_instr update)


module Cloop = struct
  type t = {
    (** Each loop has a statement id in a Cil program *)
    sid: int;
    (** The original statement of the loop *)
    mutable old_loop_stmt : Cil.stmt;
    mutable old_loop_sids : Cil.stmt IH.t;
    (** Modified body of the loop *)
    mutable new_body : Cil.stmt list;
    (** If it is a for loop the init-guard-update can be summarized*)
    mutable loop_igu : forIGU option;
    (** The file in which the loop appears *)
    mutable parent_file: Cil.file;
    (** Loops can be nested. *)
    mutable parent_loops : int list;
    mutable inner_loops : stmt list;
    (** A loop appears in the body of a parent function declared globally *)
    mutable host_function : varinfo;
    (** The set of function called in a loop body *)
    mutable called_functions : varinfo list;
    (**
        If a variable is defined as a constant / single var
       when entering the loop, this
        constant added to the mapping.
    *)
    mutable constant_in : Cil.exp IM.t;
    (** Cil's reaching definitions information *)
    mutable defined_in : defsMap;
    (** The variables used after exiting the loop *)
    mutable used_out : varinfo list;
    (** A map of variable ids to integers, to determine if the variable is in
        the read or write set. The read write set also contains temporary
        variables, therefore we do not directly define the write set as the
        state.
    *)
    mutable rwset : VS.t * VS.t;
    (**
        Some variables too keep track of the state of the work done on the loop.
        - is the loop in normal form : the loop is in normal form when the outer
        iterator is a stride-one integer.
        - is the loop body in SSA Form ?
        - does the loops contain break / continue / goto statements ?
    *)
    mutable has_breaks : bool;
  }

  let create (lstm : Cil.stmt)
      (parent : Cil.varinfo) (f : Cil.file) : t =
    { sid = lstm.sid;
      old_loop_stmt = lstm;
      old_loop_sids = IH.create 10;
      new_body = [];
      loop_igu = None;
      parent_file = f;
      parent_loops = [];
      inner_loops = [];
      host_function = parent;
      called_functions = [];
      constant_in = IM.empty;
      defined_in = IH.create 32;
      used_out = [];
      rwset = VS.empty , VS.empty;
      has_breaks = false;
    }

  let id l = l.sid

  let state l = let _ , st = l.rwset in st
  (** Parent function *)

  let setParent l par = l.host_function <- par

  let getParent l = l.host_function

  let getParentFundec l =
    check_option
      (get_fun l.parent_file l.host_function.vname)

  (** Defined variables at the loop statement*)
  let string_of_defvars l =
    let setname = "Variables defined at the entry of the loop:\n{" in
    let str = IH.fold
        (fun k (vi, dio) s -> let vS = s^" "^vi.vname in
          match dio with
          | Some mapping -> vS^"[defs]"
          | None -> vS)
        l.defined_in setname in
    str^"}"


  (**
     Setting the defined-In variables il also needed to access variable
     information in further steps. If a varaible is not "defined in" then
     we cannot access it, considering also the fact that the Cil representation
     puts all the local variable declarations in the function body at the top
     of the function, so we don't have any local variable declaration in the
     loop body.
  *)
  let setDefinedInVars l reachdefs liveset =
    let vid2v = ih_of_vs liveset in
    let r, w = l.rwset in
    let rw = VS.union r w in
    IH.iter
      (fun k ios ->
         try
           IH.add vid2v k (VSOps.find_by_id k rw)
         with Not_found -> ()) reachdefs;
    ih_join_left l.defined_in vid2v reachdefs

  let getDefinedInVars l = l.defined_in

  let add_constant_in l vid2const_map =
    l.constant_in <- IMTools.add_all l.constant_in vid2const_map
  (**
     Once the defined vars are set we can have variable information directly
     from within the Cloop module.
  *)

  let getVarinfo  ?(varname = "") l vid =
    try
      match IH.find l.defined_in vid with
      | (vi, _) -> vi
    with
      Not_found ->
      begin
        if IH.length l.defined_in < 1
        then
          raise
            (Failure
               "The defined_in are empty. Perhaps you \
                forgot initializing them ?")
        else
          raise
            (Failure
               (Printf.sprintf
                  "Failed in getVarinfo. The variable %s with id %i \
                   is not defined at the beginning of the loop.\n"
                  varname
                  vid))
      end
  (**
     Set read/write set ifnormation. The set of defined-in variables should
     be comnputed before in order to associate variable IDs with variable
     names.
  *)
  let setRW ?(checkDefinedIn = false) l (uses, defs) =
    VS.iter
      (fun v ->
         let vi = try
             getVarinfo ~varname:v.vname l v.vid
           with Failure s ->
             begin
               if checkDefinedIn
               then raise (Failure s)
               else v
             end
         in ignore(vi))
      uses;
    l.rwset <- (uses, defs)


  let string_of_rwset (cl : t) =
    let r, w = cl.rwset in
    let fmt = str_formatter in
    fprintf fmt "Read variables : %a@.Write variables: %a@."
      VSOps.pp_var_names r VSOps.pp_var_names w;
    flush_str_formatter ()


  (**
      Append a parent loop to the list of parent loops.
      The AST is visited top-down, so the list should contains
      parent loops for outermost to innermost.
  *)
  let addParentLoop l  parentSid =
    l.parent_loops <- appendC l.parent_loops parentSid

  let addChild l child =
    l.inner_loops <- appendC l.inner_loops child.old_loop_stmt

  let addCalledFunc l vi =
    l.called_functions <- appendC l.called_functions vi

  (** The loops contains either a break, a continue or a goto statement *)
  let setBreak l =
    l.has_breaks <- true

  (** Quick info *)
  let getAllVars l =
    VSOps.vs_of_defsMap l.defined_in

  let getStateVars l =
    let _, w = l.rwset in
    let vars = getAllVars l in
    VS.filter (fun v -> not v.vistmp && VS.mem v vars) w

  (** Returns true if l2 contains the loop l1 *)
  let contains l1 l2 =
    let n_in = List.mem l1.old_loop_stmt l2.inner_loops in
    let nested_in = n_in || List.mem l2.sid l1.parent_loops in
    let called_in = List.mem l1.host_function l2.called_functions  in
    nested_in || called_in

  (** Returns true if the loop contains a statements of id sid *)
  let contains_stmt l sid = IH.mem l.old_loop_sids sid

  let isForLoop l = match l.loop_igu with Some s -> true | None -> false

  let string_of_cloop (cl : t) =
    let sid = string_of_int cl.sid in
    let pfun = cl.host_function.vname in
    let cfuns = String.concat ", "
        (List.map (fun y -> y.vname) cl.called_functions) in
    let defvarS = string_of_defvars cl in
    let oigu = if isForLoop cl
      then "\n"^(sprint_igu (check_option cl.loop_igu))
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
let programFuncs = ref SM.empty
let funcRetExprs= IH.create 10

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
           SM.find v.Cloop.host_function.vname !programFuncs
         with Not_found -> raise (Failure "x")
       in
       f::l)
    programLoops []

let addGlobalFunc (fd : Cil.fundec) =
  programFuncs := SM.add fd.svar.vname fd !programFuncs

let getGlobalFuncVS () =
  VS.of_list
    (List.map (fun (a,b) -> b)
       (SM.bindings (SM.map (fun fd -> fd.svar) !programFuncs)))



(******************************************************************************)
(** LOCATIONS *)

(**
    Loop locations inspector. During a first visit of the control flow
    graph, we store the loop locations, with the containing functions
*)

class loop_finder (topFunc : Cil.varinfo) (f : Cil.file) = object
  inherit nopCilVisitor
  method vstmt (s : stmt)  =
    match s.skind with
    | Loop (b, loc, o1, o2) ->
      let cloop = (Cloop.create s topFunc f) in
      let igu, stmts = get_loop_IGU s in
      begin
        match igu with
        | Some figu ->
          if check_igu figu then
            begin
              cloop.Cloop.loop_igu <- Some figu;
              cloop.Cloop.new_body <- stmts;
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

    | Return (maybe_exp, _) ->
      (match maybe_exp with
      | Some exp -> IH.add funcRetExprs topFunc.vid exp
      | None -> ());
      SkipChildren

    | _ -> DoChildren
end ;;



let find_loops fd f : unit =
  addGlobalFunc fd;
  let visitor = new loop_finder fd.svar f in
  ignore (visitCilFunction visitor fd)


(******************************************************************************)
(** INNER BODY INSPECTION *)

(** The loop inspector inspects the body of the loop tl and adds information
    about :
    - loop nests
    - functions used
    - presence of break/gotos statements in cf *)

class loopAnalysis (tl : Cloop.t) = object
  inherit nopCilVisitor

  method vstmt (s : Cil.stmt) =
    IH.add tl.Cloop.old_loop_sids s.sid s;
    match s.skind with
    | Loop _ ->
      if Cloop.id tl != s.sid then
        (** The inspected loop is nested in the current loop *)
        begin
          let child_loop = IH.find programLoops s.sid in
          Cloop.addParentLoop child_loop (Cloop.id tl);
          Cloop.addChild tl child_loop;
          let (i, g, u) = check_option (child_loop.Cloop.loop_igu) in
          (** Remove init statements of inner loop present in outer loop *)
          let new_statements =
            rem_loop_init
              tl.Cloop.new_body [] i child_loop.Cloop.old_loop_stmt in
          tl.Cloop.new_body <- new_statements;
          DoChildren
        end
      else
        DoChildren

    | Block _ | If _ | TryFinally _ | TryExcept _
    | Goto _ | ComputedGoto _ | Break _ -> DoChildren
    | Switch _ ->
      raise
        (Failure ("Switch statement unexpected. "^
                  "Maybe you forgot to compute the CFG ?"))
    (**
       If the loop has a control-flow breaking statement, we mark the loop as
       such but stop visiting children. Currently, we do not support breaks
       and the loops will not be parallelized.
    *)
    | Continue _ | Return _->
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
let add_def_info cl vid vid2const def_id =
  try
    let stmt =
      IH.find (IHTools.convert Reachingdefs.ReachingDef.defIdStmtHash) def_id
    in
    if Cloop.contains_stmt cl stmt.sid
    (** Default action if the stmt is in the loop *)
    then raise Not_found
    (**
        Handle only the case where the statement is
        outside the loop.
    *)
    else
      match reduce_def_to_const vid stmt with
      | Some const ->
        IM.add vid const vid2const
      | None -> raise Not_found
  with Not_found ->
    vid2const

let analyze_definitions cl (x : IOS.t IH.t) =
  IH.fold
    (fun vid ioset vid2const ->
       (IOS.fold
          (fun maybe_defid vmap ->
             maybe_apply_default
               (add_def_info cl vid vmap)
               maybe_defid
               vmap)
          ioset vid2const))
    x IM.empty


let analyse_loop_context clp =
  let sid = clp.Cloop.sid in
  let fst_stmt_sid = (List.nth clp.Cloop.new_body 0).sid in
  (** Definitions reaching the loop statement *)
  let rds =
    match (Ct.simplify_rds
             (Reachingdefs.getRDs sid))
    with
    | Some x ->
      begin
        let vid2const_map = analyze_definitions clp (IHTools.convert x) in
        Cloop.add_constant_in clp vid2const_map;
        x
      end
    | None ->
      if !debug || true then
        begin
          eprintf
            "Error : analyse_loop_context - no reaching defs \
             in (sid : %i):\n %s\n"
            sid
            (Ct.psprint80 d_stmt clp.Cloop.old_loop_stmt);
          flush_all ();
        end;
      Inthash.create 2
  in
  let livevars =
    try Inthash.find LF.stmtStartData fst_stmt_sid
    with Not_found ->
      (raise (Failure "analyse_loop_context : live variables \
                       statement data not found "))
  in
  if !debug then
    begin
      printf "@.Live variables : %a@." VSOps.pvs livevars;
      printf "Keys in reaching defs :";
      IH.iter
        (fun i _ -> printf " %i " i) (IHTools.convert rds);
      printf "@.";
    end;
  if VS.cardinal livevars = 0
  then
    begin
      if !debug || true then
        begin
          eprintf
            "analyse_loop_context - no live variables in (sid : %i):\n %s\n"
            sid
            (Ct.psprint80 d_stmt clp.Cloop.old_loop_stmt);
          flush_all ();
        end;
      raise (Failure "analyse_loop_context : no live variables.");
    end
  else
    begin
      Cloop.setDefinedInVars clp (IHTools.convert rds) livevars;
      (** Visit the loop statement and compute some information *)
      visitCilStmt (new loopAnalysis clp) clp.Cloop.old_loop_stmt
    end

(******************************************************************************)
(**
   Once we have the information of the loop-nesting, we have to remove
   the termination condition of the inner loops in the outer loops, to
   do so we simply replace the body of the loop by what has already
   been computed.
   Must be executed from the bottom up in the inner-loops tree.
*)
let replace_inner_loops cl =
  let replace_matching_body stmt =
    {stmt with skind =
                 match stmt.skind with
                 | Loop (b, x, y ,loc) ->
                   let cl = IH.find programLoops stmt.sid in
                   Loop (mkBlock cl.Cloop.new_body, x, y, loc)
                 | _ -> stmt.skind}
  in
  let nstmts = List.map replace_matching_body cl.Cloop.new_body in
  cl.Cloop.new_body <- nstmts

let set_rw_info cl =
  let new_body_block = mkBlock(cl.Cloop.new_body) in
  let r = read new_body_block in
  let w = write new_body_block in
  Cloop.setRW cl (r , w) ~checkDefinedIn:false


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
  iterGlobals cfile (global_filter_only_func (fun fd -> find_loops fd cfile));
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
         set_rw_info cl;
         ignore(analyse_loop_context cl);
         vis_fids)
      programLoops []
  in
  (**
      Clean loops from innermost loop bodies to outermost
      ones. Add transformed body read/write information.
  *)
  let clean_loops =
    IHTools.iter_bottom_up
      programLoops
      (** Is a leaf if it has no nested loops *)
      (fun cl -> List.length cl.Cloop.parent_loops = 0)
      (fun cl ->
         List.map
           (fun stm -> IH.find programLoops stm.sid)
           cl.Cloop.inner_loops)
      (fun cl -> replace_inner_loops cl)
  in
  IH.clear programLoops;
  IHTools.add_list programLoops Cloop.id clean_loops;
  let loopmap =
    IH.fold
      (fun k cl m -> IM.add k cl m)
      programLoops
      IM.empty in
  IH.clear programLoops;
  loopmap, visited_funcs



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
  IH.clear funcRetExprs;
  programFuncs := SM.empty
