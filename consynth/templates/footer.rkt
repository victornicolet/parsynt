(define output-file
  (open-output-file "%output-file%" #:exists 'truncate))
(if (sat? odot)
    (begin
      (define form_list  (generate-forms odot))
      (map
       (lambda (forms)
         (displayln (syntax->datum forms) output-file))
       form_list))
    (print "unsat" output-file))
(close-output-port output-file)
