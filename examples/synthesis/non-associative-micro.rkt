#lang rosette/safe

(require consynth/lib/synthax/expressions
         consynth/lib/synthax/constructors
         rosette/lib/synthax)

(define-symbolic int_array (~> integer? real?))
(define-symbolic a b integer?)

(define (f i) (* i i))

(define (body sum from to)
  (Loop from to 4 sum (lambda (s i) (/ (+ s (f i)) 2))))

(define (join s1 l1 r1 s2 l2 r2)
  (+ (Expr s2 l2 r2 1)
     (Loop (choose l2 r2) ; start
           (choose l2 r2) ; symbolic-end
           4 ; end / loop limit
           (Expr s1 l1 r1 1) ; initial
           (lambda (s i) (/ s 2)) ; body of the loop
           )))
 

;; Synthesis problem
(define-syntax conds
  (syntax-rules ()
    [(conds a b c in) (and (eq? (join (body 0 a b) a b 0 0 0) (body 0 a b))
                             (eq? (join (body in a b) a b (body in b c) b c)
                                  (body in a c)))]))

(define cond1 (conds 2 7 9 0))
(define cond2 (conds 0 4 10 0))
(define cond3 (conds 5 12 30 0))

(define-symbolic n0 n1 n2 sum0 integer?)

(define odot 
  (time
   (synthesize
    #:forall '()
    #:guarantee (assert (and cond1 cond2 cond3)))))

(printf "Sat: ~v\n" (sat? odot))
(if (unsat? odot) (printf "Core: ~v" (core odot)) 
    (begin (printf "Forms:\n") (print-forms odot)))
