#lang rosette/safe

(require consynth/lib/synthax/expressions
         rosette/lib/synthax)

(define-symbolic int_array (~> integer? integer?))
(define-symbolic a b integer?)

(struct state (sum from to))

(define (body s from to)
  (letrec ([aux (lambda (s i to) (if (>= i to) 
                                        s
                                        (aux (/ (+ s (int_array i)) 2) (add1 i) to)) )])
    (state (aux (state-sum s) from to) from to)))

(define (join lft rgt)
  (let
      ([ato (state-to lft)]
    [bto (state-to rgt)]
    [afrom (state-from lft)]
    [bfrom (state-from rgt)]
    [a (state-sum lft)]
    [b (state-sum rgt)])
    (state (+ (/ (Expr a afrom ato 2) (expt 2 (- afrom ato))) (Expr b bfrom bto 2))
           afrom bto)))

;; Synthesis problem
(define i0 2)
(define i1 7)
(define i2 15)

(define st1 (state a i0 i1))
(define stid (state 0 0 0))
(define st2 (body stid i))

(define (state-sum-eq a b) (eq? (state-sum a) (state-sum b)))

(define odot 
  (time
   (synthesize
    #:forall (list a b)
    #:guarantee (assert (and (state-sum-eq (join st1 stid) st1)
                             (state-sum-eq (join st1 (body st2 i0 i1))
                                           (body (join st1 st2) i1 i2)))))))

(printf "Sat: ~v\n" (sat? odot))
(if (unsat? odot) (printf "Core: ~v" (core odot)) 
    (begin (printf "Forms:\n") (print-forms odot)))

