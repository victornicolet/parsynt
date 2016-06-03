#lang rosette


(define (body s0 start end)
  (letrec 
      ([aux (lambda (s i) (if (or (<= end i) (<= 10 i)) s (aux s (add1 i))))])
    (aux s0 start)))

(define-symbolic a b integer?)
(assert (and (<= 0 a) (<= a b) (<= b 10)))

(body 1 0 b) ; terminates
(body 1 a b) ; doesn't terminate
