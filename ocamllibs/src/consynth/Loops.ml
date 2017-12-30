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
let debug = ref true

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
let rds_defined_vars_set (defstbl : defsTable) = VS.vs_of_defsMap defstbl

let rds_reaching_defs_map (defstbl : defsTable) =
  IH.fold (fun vid (vi, opsid) dm ->
      match opsid with
      | Some ioset -> IM.add vid (IS.purified ioset) dm
      | None -> dm) defstbl IM.empty

(**
    The for loop statement can be stored as a triplet of
    start instruction, guard condition and nest instructions (IGU)
   for(init; guard; update) { ... }
*)
type igu = LoopsHelper.igu


(**
    Checking that the triplet is well-formed.

*)

let index_of_igu ((init, guard, update) : igu) : VS.t =
  VS.inter
    (VS.inter (VS.sovi init) (VS.sove guard))
    (VS.sovi update)

let check_igu ((init, guard, update) : igu) : bool =
  let i = index_of_igu (init, guard, update) in
  (VS.cardinal i) = 1


let sprint_igu ((init, guard, update) : igu) : string =
  sprintf "for(%s %s; %s)"
    (Ct.psprint80 Cil.dn_instr init)
    (Ct.psprint80 Cil.dn_exp guard)
    (Ct.psprint80 Cil.dn_instr update)

(* Representation of a FOR loop. Since CIL translates everything
   to their while(1) representation we have to recover the for
   loop statements nest, guard and start.
*)
type loop_repr = igu option * Cil.stmt

let empty_repr () : loop_repr = None, mkStmt(Instr [])

let update_igu ((igu, lstmt) : loop_repr) new_igu : loop_repr =
  (Some new_igu, lstmt)

let update_lstmt ((igu, lstmt) : loop_repr) new_lstmt : loop_repr =
  (igu, new_lstmt)

(**
   A loop has several variables which can be grouped into sets:
   - state variables : the variables that are written in the loop body.
   - index variables : the variables that are used as indexes in the loop.
   - used variables : variables that are read in the loop body.
   - all variables : union of all the above.
*)
type variables =
  {
    mutable state_vars : VS.t;
    mutable index_vars : VS.t;
    mutable used_vars : VS.t;
    mutable all_vars : VS.t;
    mutable tmp_vars : VS.t;
  }

let pp_variables fmt (v: variables) =
  fprintf fmt "@[<v>-State: %a@;-Index: %a@;-Used: %a@;-All: %a%a@]"
    VS.pp_var_names v.state_vars
    VS.pp_var_names v.index_vars
    VS.pp_var_names v.used_vars
    VS.pp_var_names v.all_vars
    (fun fmt vs -> if VS.is_empty vs then ()
        else VS.pp_var_names fmt vs) v.tmp_vars

let empty_variables () =
  {
    state_vars = VS.empty;
    index_vars = VS.empty;
    used_vars = VS.empty;
    all_vars = VS.empty;
    tmp_vars = VS.empty;
  }

(**
   A loop appears in a context containined:
   - lfile the host file.
   - host_function the host function.
   - parent_loops if there are nested loops, which are the loops above.
*)
type context =
  {
    lfile : file;
    host_function : varinfo;
    loc : location;
    mutable parent_loop_id : int;
    mutable reaching_definitions : defsTable;
    mutable reaching_constants : Cil.exp IM.t;
    mutable live_variables : VS.t;
  }

let pp_reaching_consts =
  PpTools.ppimap CilTools.fppe

let pp_context fmt (ctx : context) =
  fprintf fmt "@[<v>-file: %s@;-host function: %s@;-location: line %i@;\
               -reaching constants: %a@]"
    ctx.lfile.fileName ctx.host_function.vname
    ctx.loc.line
    pp_reaching_consts ctx.reaching_constants

let create_context(f : file) (hf : varinfo) (loc : location) =
  { loc = loc; lfile = f; host_function = hf; parent_loop_id = -1;
    reaching_definitions = IH.create 32; reaching_constants = IM.empty;
    live_variables = VS.empty }

(**
   All the information on the loop is grouped in the loop_info structure.
*)
type loop_info =
  {
    (* Identifier of the loop = identifier of the statement. *)
    lid : int;
    (* The loop itself. It is a for loop if the loop reprenestion has a igu. *)
    mutable lstmt : stmt;
    mutable ligu : igu option;
    (* The loop context information, used later in many places. *)
    mutable lcontext : context;
    (* The loop's variables *)
    mutable lvariables : variables;
    (* The loop's inner components *)
    mutable inner_loops : loop_info list;
    mutable called_functions : VS.t;

  }

let parent_fundec f loop =
  match get_fun f loop.lcontext.host_function.vname with
  | Some fdc -> fdc
  | None -> failwith "Loops.ml : complete_reachingdefs : \
                      failed to get fundef"


let loop_body loop =
  match loop.lstmt.skind with
  | Loop (b, _, _, _) -> b
  | _ -> failwith "Loops.ml : loop_body : Not a loop."

let loop_rwset loop =
  (loop.lvariables.used_vars, loop.lvariables.state_vars)

let create_loop (lstm: stmt) (f : file) (hf : varinfo) (loc : location) :
  loop_info =
  {
    lid = lstm.sid;
    lstmt = lstm;
    ligu = None;
    lcontext = create_context f hf loc;
    lvariables = empty_variables ();
    inner_loops = [];
    called_functions = VS.empty;
  }

let rec pp_loop fmt (loop : loop_info) =
  let pp_innerloops fmt looplist =
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@;")
      pp_loop fmt looplist
  in
  fprintf fmt "@[<v 2>Loop %i %s - %s:@;\
               @[<v 2>Body:@;@[%a@]@]@;\
               @[<v 2>Context:@;%a@]@;\
               @[<v 2>Variables:@;%a@]@;\
               @[<v 2>Inner loops:@;%a@]@;\
               @]"
    loop.lid
    (if loop.lcontext.parent_loop_id < 0 then ""
     else "(parent "^(string_of_int loop.lcontext.parent_loop_id)^")")
    (if is_some loop.ligu then sprint_igu (check_option loop.ligu) else "")
    CilTools.fppbk (loop_body loop)
    pp_context loop.lcontext pp_variables loop.lvariables
    pp_innerloops loop.inner_loops

let str_loop loop = pp_loop str_formatter loop; flush_str_formatter ()

(* Structures to store information collected in the file or across several
   files.
*)
let master_filename = ref ""
let all_loops = IH.create 10
let collect l = IH.add all_loops l.lid l
let glob_funcs = IH.create 10
let add_global fd = IH.add glob_funcs fd.svar.vid fd
let return_exprs = IH.create 10
let add_retexpr fd e = IH.add return_exprs fd.vid e
let clear () =
  master_filename := "";
  IH.clear all_loops;
  IH.clear glob_funcs

(* ========================================================================== *)
(* 1 - Collect all the loops. *)
class loopCollector (hf : varinfo) (f : file) = object
  inherit nopCilVisitor
  method vstmt (s : stmt) =
    match s.skind with
    | Loop (b, loc, o1, o2) ->
      IH.add all_loops s.sid (create_loop s f hf loc);
      (* Skip children: nested loops will be handled after. *)
      SkipChildren
    | Return (oe, _) ->
      (match oe with Some e -> add_retexpr hf e | None -> ());
      SkipChildren
    | _ -> DoChildren
end;;

let collect_loops f fd =
  add_global fd;
  let v = new loopCollector fd.svar f in ignore(visitCilFunction v fd)


(* ========================================================================== *)
(* 2 - Clean loop bodies, collect inner loops, try to get the igu *)
class loopInner (f: file) (pl : loop_info) = object
  inherit nopCilVisitor
  method vstmt (s : stmt) =
    if s.sid = pl.lid then DoChildren
    else
      match s.skind with
      | Loop(b, loc, o1, o2) ->
        (* Create the inner loop. *)
        let innerloop = create_loop s f pl.lcontext.host_function loc in
        (* Visit inner loop with a new visitor *)
        let vis = new loopInner f innerloop in
        innerloop.lstmt <- visitCilStmt vis innerloop.lstmt;
        (* Add the parent loop *)
        innerloop.lcontext.parent_loop_id <- pl.lid;
        (* Update the parent loop. *)
        pl.inner_loops <- pl.inner_loops@[innerloop];
        SkipChildren
      | _ -> DoChildren
end

class replaceInners (pl : loop_info) = object
  inherit nopCilVisitor
  method vstmt (s : stmt) =
    if List.mem s.sid (List.map (fun l -> l.lid) pl.inner_loops)
    then
      let loopname =
        Conf.inner_loop_func_name pl.lcontext.host_function.vname s.sid
      in
      let loop_f =
        Lval (Var (makeVarinfo false loopname (TInt(IInt, []))), NoOffset)
      in
      let call_loop = Call (None, loop_f, [], locUnknown) in
      let call_loop_stmt = Instr ([call_loop]) in
      ChangeTo {s with skind = call_loop_stmt}
    else
      DoChildren
end

let clean_loop_bodies f () =
  let rec clean_loop_body lid loop =
    (* ------------------------------------------------------------ *)
    (* Look for inner loops, clean the inner body of the statements
       inserted by Cil. *)
    let fetch_inner_loops loop =
      let vis = new loopInner f loop in
      loop.lstmt <- visitCilStmt vis loop.lstmt
    in
    let clean_for_loops loop =

      let inits_to_remove = IH.create 10 in
      (* Get the igu of all loops, and if not None, treat it as a for loop:
         - remove the index increment.
      *)
      let rec get_igu loop =
        loop.inner_loops <- List.map get_igu loop.inner_loops;
        let maybe_igu, inner_body = get_loop_IGU loop.lstmt in
        match maybe_igu with
        | Some (init, g, u) ->
          (* The loop is a for loop. *)
          begin
            loop.ligu <- maybe_igu;
            loop.lstmt <-
              CilTools.replace_loop_block loop.lstmt (mkBlock(inner_body));
            IH.add inits_to_remove
              loop.lcontext.parent_loop_id (init,loop.lstmt);
            loop
          end
        (* The loop is a while loop. Do not modify. *)
        | None ->
          begin
            loop
          end
      in

      (* Remove the init statements of for loops in the outer loop (only one
         level of recursion) *)
      let rec clean_init_statements loop =
        loop.inner_loops <- List.map clean_init_statements loop.inner_loops;
        try
          let remv = IH.find_all inits_to_remove loop.lid in
          loop.lstmt <-
            CilTools.replace_loop_block loop.lstmt
              (rem_loop_init (loop_body loop) remv);
          loop
        with Not_found -> loop
      in

      (* Replace inner for loops by a function call *)
      let rec replace_inners loop =
        loop.inner_loops <- List.map replace_inners loop.inner_loops;
        let vis = new replaceInners loop in
        loop.lstmt <- visitCilStmt vis loop.lstmt;
        loop
      in

      (get_igu --> clean_init_statements --> replace_inners) loop
    in
    fetch_inner_loops loop;
    IH.replace all_loops loop.lid (clean_for_loops loop)
  in
  IH.iter clean_loop_body all_loops

(* ========================================================================== *)
(* 3 - Get all the variables *)
let rmtmps = VS.filter (fun v -> not v.vistmp)
let tmps = VS.filter (fun v -> v.vistmp)

let analyze_loop_bodies cfile () =
  let analyze_loop lid loop =
    let rec populate_varsets loop =
      loop.inner_loops <- List.map populate_varsets loop.inner_loops;
      let r = va_read (loop_body loop) in
      let w = va_write (loop_body loop) in
      (* State variables : written in body + in nested loops *)
      loop.lvariables.state_vars <-
        VS.union w
          (VS.unions (List.map (fun loop -> loop.lvariables.state_vars)
                        loop.inner_loops));
      (* Used variables : read in body + in nested loops *)
      loop.lvariables.used_vars <-
        VS.union r
          (VS.unions (List.map (fun loop -> loop.lvariables.used_vars)
                        loop.inner_loops));
      (* Index variables: the index of the enclosing for. *)
      (match loop.ligu with
      | Some igu ->
        loop.lvariables.index_vars <- index_of_igu igu
      | None -> ());
      (* All variables: union of all previous. *)
      loop.lvariables.all_vars <-
        VS.unions [loop.lvariables.state_vars;
                   loop.lvariables.used_vars;
                   loop.lvariables.index_vars];
      (* Remove temporaries *)
      loop.lvariables <- {
        state_vars = rmtmps loop.lvariables.state_vars;
        index_vars = rmtmps loop.lvariables.index_vars;
        used_vars = rmtmps loop.lvariables.used_vars;
        all_vars = rmtmps loop.lvariables.all_vars;
        tmp_vars = tmps loop.lvariables.all_vars
      };
      loop
    in
    IH.replace all_loops loop.lid (populate_varsets loop)
  in
  IH.iter analyze_loop all_loops


(* ========================================================================== *)
(* 4 - Get advanced context information: live variables, reaching expressions *)

(* Remove temporary variables introduced by Cil in reaching definitions. *)

let remove_temps (map : exp IM.t) =
  IM.map
    (fun e ->
       match e with
       | Lval (Var vi, NoOffset) when vi.vistmp ->
         IM.find vi.vid map
       | _ -> e) map


let add_def_info loop vid vid2const def_id =
  let stmt =
    IH.find (IHTools.convert Reachingdefs.ReachingDef.defIdStmtHash) def_id
  in
  try
    match reduce_def_to_const vid stmt with
    | Some const -> IM.add vid const vid2const
    | None -> vid2const
  with Init_with_temp vi ->
    IM.add vid (Cil.Lval (Var vi, NoOffset)) vid2const

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

let complete_reachingdefs f =
  let populate_reachdefs lid loop =
    let parent_fundec =
      match get_fun f loop.lcontext.host_function.vname with
      | Some fdc -> fdc
      | None -> failwith "Loops.ml : complete_reachingdefs : \
                          failed to get fundef"
    in
    Reachingdefs.computeRDs parent_fundec;
    let set_rd_of_loop loop =
      (** Definitions reaching the loop statement *)
      match (Ct.simplify_rds (Reachingdefs.getRDs loop.lid)) with
      | Some x ->
        begin
          let vid2const_map =
            remove_temps (analyze_definitions loop (IHTools.convert x)) in
          loop.lcontext.reaching_constants <- vid2const_map
        end
      | None ->
        if !debug || true then
          begin
            eprintf
              "Error : analyse_loop_context - no reaching defs \
               in (sid : %i):\n %s\n"
              loop.lid
              (Ct.psprint80 d_stmt loop.lstmt);
            flush_all ();
          end
    in
    List.iter set_rd_of_loop loop.inner_loops;
    set_rd_of_loop loop
  in
  IH.iter populate_reachdefs all_loops

(* ========================================================================== *)
(* MAIN ENTRY POINTS -- *)
let process_file cfile =
  master_filename := cfile.fileName;
  iterGlobals cfile (global_filter_only_func (collect_loops cfile));
  clean_loop_bodies cfile ();
  analyze_loop_bodies cfile ();
  complete_reachingdefs cfile

let get_loops () =
  if (!master_filename = "") then
    raise (Failure "No file processed, no loop data!")
  else
    all_loops
