open Format
open Utils
open FPretty
open PpTools

module C = Canalyst
module C2F = Cil2Func
module S = Sketch


let test loopsm =
  printf "%s--------TEST Func ---> Sketch%s@." (color "red") color_default;
  SM.iter
    (fun fname vals ->
       let vs, igu, func = vals in
       let builder = new S.Body.sketch_builder vs vs func igu in
       builder#build;
       let body_form, sigu = check_option builder#get_sketch in
       printf"%s%s%s : @; %a@." (color "green") fname color_default
         pp_fnlet body_form;
       let join = S.Join.build vs body_form in
       printf"Join : @; %a@."
         pp_fnlet join
    )
    loopsm
