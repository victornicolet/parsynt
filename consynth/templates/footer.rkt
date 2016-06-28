(define forms (car (generate-forms odot)))
(define solution-out (open-output-file "%output-file%" #:exists 'truncate))
   (write (syntax->datum forms) solution-out)
   (close-output-port solution-out)
