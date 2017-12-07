open Consynth
open Cil
open FpExpansions

module Sk = Consynth.SketchTypes


(* Generate header file for  corresponding floating point expansion *)
let fpexp_header sketch = FpExpansions.gen_header sketch
(* Generate header and source  *)
