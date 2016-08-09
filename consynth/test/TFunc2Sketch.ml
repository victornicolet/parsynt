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
      let body_form = S.Build.build_body func vs in
      printf"%s%s%s : @; %a@." (color "green") fname default
        pp_sklet body_form;
      let join = S.Build.build_join body_form vs in
      printf"Join : @; %a@."
         pp_sklet join
    )
    loopsm
