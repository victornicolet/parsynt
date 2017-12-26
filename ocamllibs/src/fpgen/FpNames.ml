open Utils
open Format
open Cil

module Ppt = PpTools


let superacc_vi (vi : varinfo) =
  {vi with vname = vi.vname^"_superacc"}

let fpexp_vi (vi : varinfo) =
  {vi with vname = vi.vname^"_exp"}
