#lang rosette

(require "./expressions.rkt")

(provide Loopsc Loop)

(define loop-limit 200)

(define-syntax Loop
  (syntax-rules ()
    [(Loop start end limit initial body) 
     (begin (assert (and (<= start end) (<= 0 start) (<= end loop-limit)))
            (Loopsc start end limit initial body))]))

(define-syntax Loopsc
  (syntax-rules ()
    ;; generates the loop with the (e s) as body, iterated from a to b
    [(Loopsc start end initial body) 
     (letrec 
         ([aux (lambda (s i) (if (>= i end) s (aux (body s i) (add1 i))))])
       (aux initial start))]
    [(Loopsc start symbolic-end end initial body)
     (letrec 
         ([aux (lambda (s i) 
                 (if (or (>= i end) (>= i symbolic-end)) s (aux (body s i) (add1 i))))])
       (aux initial start))]))
