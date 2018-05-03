#lang rosette

(require "./expressions.rkt")

(provide Loopsc Loop LoopFunc)

(define loop-limit 64)

(define-syntax Loop
  (syntax-rules ()
    [(Loop start end limit initial body)
     (begin (assert (and (<= start end) (<= 0 start) (<= end loop-limit)))
            (Loopsc start end limit initial body))]
    [(Loop start end initial body)
     (begin (assert (and (<= start end) (<= 0 start) (<= end loop-limit)))
            (Loopsc start end 10 initial body))]))


(define-syntax LoopFunc
  (syntax-rules ()
    [(LoopFunc i_val i_guard i_update input_state loop_body)
     (letrec
         ([aux (lambda (s i) (if (i_guard i) (aux (loop_body s i) (i_update i)) s))])
       (aux input_state i_val))]))

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
