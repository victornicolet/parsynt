open Base
open Lib.Front.C
open Lang.Term
open Lang.Typ
open Getopt
open Fmt
open Lib

let always_lift = ref false

let tstart = ref 0.0

let help () =
  Fmt.pf stdout
    "usage: ./Discure INPUT_FILE [-h] [-k K -m M -c C] [-v] [-d D] [-P] [--quiet] [--dump] \n\
    \                            [--two-pivots] [--no-break] \n\
    \  Optional arguments:\n\
    \  -h, --help           show this help message and exit\n\
    \  -k K -m M -c C       search for solutions within a specified budget (ignored for \n\
    \                       single loops)\n\
    \  -v --verbose         verbose output (prints intermediary information)\n\
    \  -d, --debug D        output for debugging with verbosity level\n\
    \  -P                   only parse the input (check syntax)\n\
    \  --quiet              no output except execution time\n\
    \  --dump               dump solutions in text file\n\
    \  --two-pivots         force search of partitions with two pivots (ignored for single \n\
    \                       loops)\n\
    \  --no-break           do not break join into subproblems (try for small problems and\n\
    \                       few cores)\n\
     See input examples in inputs/table1/*.minic and inputs/table7a/*.minic. E.g. run:\n\
     ./Discure inputs/table7a/lmo.minic\n"

let options =
  [
    ( 'h',
      "help",
      Some
        (fun () ->
          help ();
          Caml.exit 0),
      None );
    ('d', "debug", None, Some (fun l -> Log.verb_debug := Int.of_string l));
    ('P', "parse-only", set Config.parse_minic_only true, None);
    ('q', "quiet", set Log.quiet true, None);
    ('v', "verbose", set Log.verbose true, None);
    ('w', "warning", set Log.verb_warning true, None);
    ('\000', "no-break", set Config.break_problem false, None);
    ('\000', "div-synt", None, Some (fun l -> Solve.DivideSketches.divide_len := Int.of_string l));
    ('\000', "dump", set Config.dump_solutions true, None);
    ('\000', "two-pivots", Some Recursion.SketchBuilders.force_two_pivots, None);
    (* Search for a single budget *)
    ('k', "join-complexity", None, Some Config.set_k);
    ('m', "join-arity", None, Some Config.set_m);
    ('c', "divide-image", None, Some Config.set_c);
  ]

let fgt d s fmt () = pf fmt d s

let parse_input filename =
  Log.info (Utils.string_msg "Parsing %s." filename);
  if !Config.minic_input then
    try
      let fl = get_problems filename in
      let loops_as_funcs =
        List.map
          ~f:(fun (args, body, outset) -> (mk_lambda (Set.to_list args) body, outset))
          fl.lf_loops
      in
      (loops_as_funcs, fl.lf_asserts)
    with e -> raise e
  else
    let file, _ = Scripting.parse_file_with_defs filename in
    if !Log.verbose then (List.map ~f:(fun x -> (x, VarSet.empty)) file.expressions, [])
    else ([], [])

let to_dnc (sp_or_sfsp : (Lang.E.soln_info, float * (VarSet.t * term) list * term) Either.t) =
  match sp_or_sfsp with
  | Either.First sln -> (
      try
        match Recursion.SelfFoldSinglePass.solve sln with
        | [] ->
            let elapsed = Unix.gettimeofday () -. !tstart in
            Log.warning (fun f () ->
                Fmt.pf f "No solution found for problem in %s." !Config.master_file);
            if !Log.quiet then Log.print_res_unsat !Config.master_file elapsed
        | l ->
            List.iter
              ~f:(fun f ->
                Log.success (fun frmt () ->
                    Fmt.pf frmt "Solution(%s):@.%a" !Config.master_file Lang.E.pp_join_soln f);
                if !Log.quiet then
                  let dsynt = match f.divide with Some d -> d.synt_time | _ -> 0.0 in
                  Log.print_res_timing !Config.master_file f.budget.k f.budget.m f.budget.c
                    sln.synt_time f.pred_synt_time dsynt f.synt_time)
              l
      with e ->
        if !Log.quiet then
          let elapsed = Unix.gettimeofday () -. !tstart in
          Log.print_res_error !Config.master_file elapsed
        else raise e)
  | Either.Second (stime, asserts, b) -> (
      let r_eqns = Recursion.EquationSystems.solve asserts b in
      let elapsed = Unix.gettimeofday () -. !tstart in
      match r_eqns with
      | Some soln ->
          Log.success (fun f () -> pf f "Equation system:@;@[%a@]" Lang.E.pp_l_eqns soln);
          if !Log.quiet then
            Log.print_res_timing !Config.master_file 0 2 2 stime soln.synt_time_lift 0.
              soln.synt_time_join
      | None ->
          Log.error (Utils.wrap "No solution found.");
          if !Log.quiet then Log.print_res_unsat !Config.master_file elapsed;
          Caml.exit 0)

let main () =
  let argv = Sys.get_argv () in
  parse_cmdline options (fun s -> Config.master_file := s);
  set_style_renderer stdout `Ansi_tty;
  Stdlib.Format.pp_set_margin stdout 80;
  Fmt.set_utf_8 stdout true;
  Log.info (Utils.wrap "Starting.");
  (* Parse the input file *)
  if Array.length argv < 2 then (
    Log.error (Utils.wrap "Usage: ./Discure FILENAME");
    failwith "Specify input file name to Discure.")
  else (
    tstart := Unix.gettimeofday ();
    let parsed_input, asserts = parse_input !Config.master_file in
    Log.success (fun fmt () -> pf fmt "Parsed %s." !Config.master_file);
    if !Config.parse_minic_only then Caml.exit 0;
    let spass_funcs =
      List.map ~f:(Recursion.SelfFoldSinglePass.to_single_pass asserts) parsed_input
    in
    let _ = List.map ~f:to_dnc spass_funcs in
    Log.success (fun fmt () -> pf fmt "Finished."))

;;
main ()
