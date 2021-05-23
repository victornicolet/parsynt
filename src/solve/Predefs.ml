open Base
open Fmt
open Lang.Typ

let pp_lang_def_rosette (form : Formatter.t) () =
  pf form "#lang rosette@.";
  pf form "@.";
  pf form "(require rosette/lib/synthax)"

let pp_newline (form : Formatter.t) () =
  pf form "@."

let pp_separator_line (form : Formatter.t) () =
  pf form ";; <----------------------------------> @."

let pp_list_as_set_equality (form : Formatter.t) () =
  let def =
    "(define (equal-sets? l1 l2)
  (let
      ([l1 (remove-duplicates l1)]
       [l2 (remove-duplicates l2)])
    (let
        ([not_in (lambda (l) (lambda (x) (not (list? (member x l)))))])
      (and (null? (filter (not_in l1) l2))
           (null? (filter (not_in l2) l1))))))"
  in
  pf form "%s@." def


let pre_pp_struct_defs fout struct_types =
  List.iter
    ~f:(fun t -> pf fout "@.%a@." (box pp_struct_def) t)
    (Set.to_list struct_types)


let pp_output_sketch_to_file ~(file_out : string) ~(obj : string) fout () =
  pf fout
    "@.(define output-file (open-output-file \"%s\" #:exists 'truncate))@."
    file_out;
  pf fout "(println ' output-file)@.";
  pf fout
    "(if (sat? %s)
      (begin
        (define form_list  (generate-forms %s))
        (if (empty? form_list)
          (println \"sat\" output-file)
          (map
            (lambda (forms)
              (println (syntax->datum forms) output-file))
              form_list)))
      (println \"unsat\" output-file))
   (close-output-port output-file)@."
    obj obj;
  pf fout
    ";;(if (sat? %s) (print-forms %s) (println \"unsat\"))@."
    obj obj;