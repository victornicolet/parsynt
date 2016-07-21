open Format
open Utils
open SPretty
open PpHelper

module C = Canalyst
module C2F = Cil2Func
module S = Sketch


let test loopsm =
  printf "%s--------TEST Func ---> Sketch%s@." (color "red") default;
  SM.iter
    (fun fname vals ->
      let vs, func = vals in
      let sketch_form = S.build_sketch func vs in
      printf"%s%s%s : @; %a@." (color "green") fname default
        pp_sklet sketch_form)
    loopsm
