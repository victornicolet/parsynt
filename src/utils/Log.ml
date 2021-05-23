open Base
open Fmt

(* Logging and printing messages. *)
let quiet = ref false

let verbose = ref false

let verb_debug = ref 0

let verb_warning = ref false

let submsg_on = ref false

let indent () = if !submsg_on then "\t" else ""

(* Logging and messaging *)
let error (msg : unit t) =
  if not !quiet then
    let styled_bold_bgred s = styled `Black (styled (`Bg `Red) s) in
    pf stdout "%s@[%a %a@]@." (indent ()) (styled_bold_bgred string) "  ERROR  " (box msg) ()

let info (msg : unit t) =
  if (not !quiet) && !verbose then
    let styled_bold_bgred s = styled `Black (styled (`Bg `Cyan) s) in
    pf stdout "%s@[%a %a@]@." (indent ()) (styled_bold_bgred string) "   INFO  " (box msg) ()
  else ()

let debug ?(level = 0) (msg : unit t) =
  if (not !quiet) && level < !verb_debug then
    let styled_bold_bgred s = styled `Black (styled (`Bg `Blue) s) in
    pf stdout "%s@[%a %a@]@." (indent ()) (styled_bold_bgred string) "  DEBUG  " (box msg) ()
  else ()

let success (msg : unit t) =
  if not !quiet then
    let styled_bold_bgred s = styled `Bold (styled `Black (styled (`Bg `Green) s)) in
    pf stdout "%s@[%a %a@]@." (indent ()) (styled_bold_bgred string) " SUCCESS " (box msg) ()

let warning ?(level = 0) (msg : unit t) =
  if (not !quiet) && level < !verb_debug then
    let styled_bold_bgred s = styled `Bold (styled `Black (styled (`Bg `Yellow) s)) in
    if !verbose then
      pf stdout "%s@[%a %a@]@." (indent ()) (styled_bold_bgred string) " WARNING " (box msg) ()

let warning_msg ?(level = 0) msg = warning ~level (fun f () -> pf f "%s" msg)

let error_msg msg = error (fun f () -> pf f "%s" msg)

let debug_msg ?(level = 0) msg = debug ~level (fun f () -> pf f "%s" msg)

let info_msg msg = info (fun f () -> pf f "%s" msg)

let success_msg msg = success (fun f () -> pf f "%s" msg)

let print_res_timing file k m c fsynt psynt dsynt jsynt =
  let fn = Caml.Filename.basename file in
  pf stdout "%s,%i,%i,%i,%.3f,%.3f,%.3f,%.3f@." fn k m c fsynt psynt dsynt jsynt

let print_res_unsat file elapsed =
  let fn = Caml.Filename.basename file in
  pf stdout "%s,0,0,0,%.3f,unsat,unsat,unsat@." fn elapsed

let print_res_error file elapsed =
  let fn = Caml.Filename.basename file in
  pf stdout "%s,-1,-1,-1,%.3f,err,err,err@." fn elapsed
