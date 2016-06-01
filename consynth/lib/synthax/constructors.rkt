#lang rosette

(require "./expressions.rkt")

(provide loopsc)

(define-syntax loopsc
  (syntax-rules ()
    ;; generates the loop with the (e s) as body, iterated from a to b
    [(loopsc e s0 a b) 
     (letrec 
         ([aux (lambda (s i) (if (>= i b) s (aux (e s) (add1 i) b)))])
       (aux s0 a))]))
