open Cil
open Format
open LoopsHelper
open Utils
open Utils.ListTools
open Utils.PpTools
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
   From Cil's documentation:
   The third member is a mapping from variable IDs to Sets of integer options.
   If the set contains Some(i), then the definition of that variable with ID i
   reaches that statement. If the set contains None, then there is a path to
   that statement on which there is no definition of that variable. Also, if
   the variable ID is unmapped at a statement, then no definition of that
   variable reaches that statement.
*)
type defsTable = (VS.elt * (IOS.t option))  IH.t

(** Some useful function to deal with reaching definitions *)
let rds_defined_vars_set (defstbl : defsTable) = VSOps.vs_of_defsMap defstbl

let rds_reaching_defs_map (defstbl : defsTable) =
  IH.fold (fun vid (vi, opsid) dm ->
      match opsid with
      | Some ioset -> IM.add vid (purify ioset) dm
      | None -> dm) defstbl IM.empty

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


type loop_rep = {
  mutable lstmt : Cil.stmt;
  mutable lanalyzed : bool;
  mutable lsids : Cil.stmt IH.t;
}

let create_empty_rep () = {
  lstmt = Cil.mkEmptyStmt ();
  lanalyzed = false;
  lsids = IH.create 1;
}

let update_loop_body rep block =
  let new_loop = Ct.replace_loop_block rep.lstmt block in
  {
    lstmt = new_loop;
    lsids = Ct.collect_sids new_loop;
    lanalyzed = false;
  }

module Cloop = struct
  type t = {
    (** Each loop has a statement id in a Cil program *)
    sid: int;
    (** The original statement of the loop *)
    mutable old_loop : loop_rep;
    (** Modified loop *)
    mutable new_loop : loop_rep;
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
    mutable called_functions : VS.t;
    (** Cil's reaching definitions information *)
    mutable reaching_definitions : defsTable;
    mutable reaching_constant_definitions : Cil.exp IM.t;
    (** The variables used after exiting the loop *)
    mutable live_variables : VS.t;
    (** Read - write set. *)
    mutable rwset : VS.t * VS.t;
    mutable tmps : VS.t;
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
      old_loop = {
        lstmt = lstm;
        lanalyzed = false;
        lsids = Ct.collect_sids lstm;
      };
      new_loop = create_empty_rep ();
      loop_igu = None;
      parent_file = f;
      parent_loops = [];
      inner_loops = [];
      host_function = parent;
      called_functions = VS.empty;
      reaching_definitions = IH.create 32;
      reaching_constant_definitions = IM.empty;
      live_variables = VS.empty;
      rwset = VS.empty , VS.empty;
      tmps = VS.empty;
      has_breaks = false;
    }

  let id l = l.sid

  (** Parent function *)

  let set_parent_func l par = l.host_function <- par

  let get_parent_func l = l.host_function

  let parent_fundec l =
    check_option
      (get_fun l.parent_file l.host_function.vname)

  let add_constant_in l vid2const_map =
    l.reaching_constant_definitions <-
      IM.add_all l.reaching_constant_definitions vid2const_map

  (* Get the variable from the reaching definitions *)
  let get_varinfo  ?(varname = "") l vid =
    VS.max_elt
      (VS.filter
         (fun vi ->
            (vid = vi.vid && (varname = "" ||  vi.vname = varname)))
         (rds_defined_vars_set l.reaching_definitions))


  (* Access the state, and update it *)
  let state l =
    let rt , st = l.rwset in
    let nst = VS.filter (fun vi -> not vi.vistmp) st in
    l.tmps <- VS.filter (fun vi -> vi.vistmp) st;
    l.rwset <- (rt, nst);
    nst


  let set_rw ?(checkDefinedIn = false) l (uses, defs) =
    if checkDefinedIn then
        VS.iter
        (fun v ->  try
            ignore(get_varinfo ~varname:v.vname l v.vid)
          with Failure s ->
            failwith "Variable not defined in")
        uses;
    l.tmps <- VS.filter (fun vi -> vi.vistmp) (VS.union uses defs);
    l.rwset <- (uses, defs)


  let string_of_rwset (cl : t) =
    let r, w = cl.rwset in
    let fmt = str_formatter in
    fprintf fmt "Read variables : %a@.Write variables: %a@."
      VSOps.pp_var_names r VSOps.pp_var_names w;
    flush_str_formatter ()


  let set_live_vars clp livevars = clp.live_variables <- livevars
  (**
      Append a parent loop to the list of parent loops.
      The AST is visited top-down, so the list should contains
      parent loops for outermost to innermost.
  *)
  let add_parent_loop l  parentSid =
    l.parent_loops <- appendC l.parent_loops parentSid

  let add_child_loop l child =
    l.inner_loops <- appendC l.inner_loops child.old_loop.lstmt

  let add_callee l vi =
    l.called_functions <- VS.add vi l.called_functions

  (** The loops contains either a break, a continue or a goto statement *)
  let set_break l =
    l.has_breaks <- true

  (** Quick info *)
  let all_vars l =
    rds_defined_vars_set l.reaching_definitions

  (* Loop bodies *)
  let new_body l = Ct.extract_block l.new_loop.lstmt
  let old_body l = Ct.extract_block l.old_loop.lstmt

  let update_new_loop_block l block =
    l.new_loop <- update_loop_body l.new_loop block

  (** Returns true if l2 contains the loop l1 *)
  let contains l1 l2 =
    let n_in = List.mem l1.old_loop.lstmt l2.inner_loops in
    let nested_in = n_in || List.mem l2.sid l1.parent_loops in
    let called_in =
      List.mem l1.host_function (VSOps.varlist l2.called_functions)
    in
    nested_in || called_in

  (** Returns true if the loop contains a statements of id sid *)
  let contains_stmt l sid =
    IH.mem l.old_loop.lsids sid

  let is_for_loop l = match l.loop_igu with Some s -> true | None -> false

  let __str__ (cl : t) =
    let sid = string_of_int cl.sid in
    let pfun = cl.host_function.vname in
    let cfuns = String.concat ", "
        (VSOps.vsmap (fun y -> y.vname) cl.called_functions) in
    let defvarS = "<WIP>" in
    let oigu = if is_for_loop cl
      then "\n"^(sprint_igu (check_option cl.loop_igu))
      else ""
    in
    let rwsets = string_of_rwset cl in
    sprintf "---> Loop %s in %s:\nCalls: %s\n%s%s\n%s"
      sid pfun cfuns defvarS oigu rwsets
end

(******************************************************************************)

(** Each loop is stored with the statement id *)
let fileName = ref ""
(* All the loops in the program file *)
let program_loops = IH.create 10
(* All the functions in the program file *)
let program_funcs = ref SM.empty
(* Hash : function id -> return expressions *)
let return_exprs= IH.create 10

let clearLoops () =
  IH.clear program_loops

(* Add a loop to the program *)
let add_loop (loop : Cloop.t) : unit =
  IH.add program_loops loop.Cloop.sid loop

(* Returns true if the loop belongs to the program analyzed *)
let has_loop (loop : Cloop.t) : bool =
  IH.mem program_loops loop.Cloop.sid

(* Returns the list of functions containing loops *)
let get_function_with_loops () : Cil.fundec list =
  IH.fold
    (fun k v l ->
       let f =
         try
           SM.find v.Cloop.host_function.vname !program_funcs
         with Not_found -> raise (Failure "x")
       in
       f::l)
    program_loops []

(* Add a function in the map program_funcs *)
let addGlobalFunc (fd : Cil.fundec) =
  program_funcs := SM.add fd.svar.vname fd !program_funcs

let getGlobalFuncVS () =
  VS.of_list
    (List.map (fun (a,b) -> b)
       (SM.bindings (SM.map (fun fd -> fd.svar) !program_funcs)))



(******************************************************************************)
(** LOCATIONS *)

(**
    Loop locations inspector. During a first visit of the control flow
    graph, we store the loop locations, with the containing functions
*)

class loop_finder (top_func : Cil.varinfo) (f : Cil.file) = object
  inherit nopCilVisitor
  method vstmt (s : stmt)  =
    match s.skind with
    | Loop (b, loc, o1, o2) ->
      let cloop = (Cloop.create s top_func f) in
      let igu, stmts = get_loop_IGU s in
      let new_loop =
        Ct.replace_loop_block cloop.Cloop.old_loop.lstmt (mkBlock(stmts)) in
      begin
        match igu with
        | Some figu ->
          if check_igu figu then
            begin
              cloop.Cloop.loop_igu <- Some figu;
              cloop.Cloop.new_loop <-
                {
                  lstmt = new_loop;
                  lsids = Ct.collect_sids new_loop;
                  lanalyzed = true;
                }
            end
          else ()
        | _ -> ()
      end;
      add_loop cloop;
      DoChildren

    | Block _ | If _ | TryFinally _ | TryExcept _ ->
      DoChildren
    | Switch _ ->
      raise
        (Failure ("Switch statement unexpected. "^
                  "Maybe you forgot to compute the CFG ?"))

    | Return (maybe_exp, _) ->
      (match maybe_exp with
      | Some exp -> IH.add return_exprs top_func.vid exp
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
    tl.Cloop.old_loop.lanalyzed <- true;
    IH.add tl.Cloop.old_loop.lsids s.sid s;
    match s.skind with
    | Loop _ ->
      if Cloop.id tl != s.sid then
        (** The inspected loop is nested in the current loop *)
        begin
          let child_loop = IH.find program_loops s.sid in
          Cloop.add_parent_loop child_loop (Cloop.id tl);
          Cloop.add_child_loop tl child_loop;
          let (index, g, u) = check_option (child_loop.Cloop.loop_igu) in
          (** Remove init statements of inner loop present in outer loop *)
          let new_statements =
            rem_loop_init
              (Ct.extract_block tl.Cloop.new_loop.lstmt)
              []
              index
              child_loop.Cloop.old_loop.lstmt
          in
          Cloop.update_new_loop_block tl  new_statements;
          DoChildren
        end
      else
        DoChildren

    | Block _ | If _ | TryFinally _ | TryExcept _   | Instr _
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
      Cloop.set_break tl;
      SkipChildren

  method vinst (i : Cil.instr) : Cil.instr list Cil.visitAction =
    match i with
    | Call (lval_opt, ef, elist, _)  ->
      begin
        match ef with
        | Lval (Var vi, _) -> Cloop.add_callee tl vi
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
exception Skip_action


let rec add_def_info cl vid vid2const def_id =
  if not cl.Cloop.old_loop.lanalyzed then failwith "Uninitalized information.";
  try
    let stmt =
      IH.find (IHTools.convert Reachingdefs.ReachingDef.defIdStmtHash) def_id
    in
    if Cloop.contains_stmt cl stmt.sid
    (** Default action if the stmt is in the loop *)
    then raise Skip_action
    (**
        Handle only the case where the statement is
        outside the loop.
    *)
    else
      try
        match reduce_def_to_const vid stmt with
        | Some const -> IM.add vid const vid2const
        | None -> raise Skip_action
      with Init_with_temp vi ->
        IM.add vid (Cil.Lval (Var vi, NoOffset)) vid2const
  with Skip_action -> vid2const

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

let remove_temps (map : exp IM.t) =
  IM.map
    (fun e ->
       match e with
       | Lval (Var vi, NoOffset) when vi.vistmp ->
         IM.find vi.vid map
       | _ -> e) map

let analyse_loop_context clp =
  ignore(visitCilStmt (new loopAnalysis clp) clp.Cloop.old_loop.lstmt);
  let sid = clp.Cloop.sid in
  let fst_stmt_sid = (List.nth (Cloop.new_body clp).bstmts 0).sid in
  (** Definitions reaching the loop statement *)
  let rds =
    match (Ct.simplify_rds (Reachingdefs.getRDs sid)) with
    | Some x ->
      begin
        let vid2const_map =
          remove_temps (analyze_definitions clp (IHTools.convert x)) in
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
            (Ct.psprint80 d_stmt clp.Cloop.old_loop.lstmt);
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
            (Ct.psprint80 d_stmt clp.Cloop.old_loop.lstmt);
          flush_all ();
        end;
      raise (Failure "analyse_loop_context : no live variables.");
    end
  else
    begin
      Cloop.set_live_vars clp livevars
    end

(******************************************************************************)
(* Set the read-write set info of the loop body *)
let set_rw_info cl =
  let new_body_block = Cloop.new_body cl in
  let r = va_read new_body_block in
  let w = va_write new_body_block in
  Cloop.set_rw cl (r , w) ~checkDefinedIn:false


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
  (try
    iterGlobals cfile (global_filter_only_func (fun fd -> find_loops fd cfile))
  with Not_found ->
    raise (Failure ("Not_found in iterGLobals to find loops")));
  (**
     Visit each function containing a loop, but compute cil information
     like Reaching defintions and live variables each time the function
     is visited.
  *)
  let visited_funcs =
    IH.fold
      (fun k cl visited_fids ->
         let fdc = Cloop.parent_fundec cl in
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
      program_loops []
  in
  (**
      Clean loops from innermost loop bodies to outermost
      ones. Add transformed body read/write information.
  *)
  let clean_loops =
    IHTools.iter_bottom_up
      program_loops
      (** Is a leaf if it has no nested loops *)
      (fun cl -> List.length cl.Cloop.parent_loops = 0)
      (fun cl ->
         List.map
           (fun stm -> IH.find program_loops stm.sid)
           cl.Cloop.inner_loops)
      (fun cl -> ())
  in
  IH.clear program_loops;
  IHTools.add_list program_loops Cloop.id clean_loops;
  let loopmap =
    IH.fold
      (fun k cl m -> IM.add k cl m)
      program_loops
      IM.empty in
  IH.clear program_loops;
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
    program_loops

let clear () =
  fileName := "";
  clearLoops ();
  IH.clear return_exprs;
  program_funcs := SM.empty
