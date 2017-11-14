open Z3engine
open SketchTypes
open Cil
open Utils
open TestUtils

let x, y, z, a, b, c, a_n =
  (make_int_varinfo "x"),
  (make_int_varinfo ~init:one "y"),
  (make_int_varinfo "z"),
  (make_int_varinfo "a"),
  (make_bool_varinfo ~init:cil_false "b"),
  (make_bool_varinfo "c"),
  (make_int_array_varinfo "a_n")


let main () =
  let stv = VSOps.of_varlist [x; y; z] in
  let ovars = VSOps.of_varlist [a; b; c; a_n] in
  let allvars = VS.union ovars stv in
  let sctx = mk_ctx allvars stv in
  let z3e = new engine sctx in
  z3e#start ();
