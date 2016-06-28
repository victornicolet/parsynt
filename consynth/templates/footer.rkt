(define output-file
  (open-output-file "%output-file%" #:exists 'truncate))
(if (sat? odot)
    (begin
      (define forms (car (generate-forms odot)))
      (write (syntax->datum forms) output-file))
    (print "unsat" output-file))
(close-output-port output-file)
