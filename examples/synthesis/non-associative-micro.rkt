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
  (+ (choose s2 l2 r2 2)
     (Loop (choose l2 r2) ; start
             (choose l2 r2) ; symbolic-end
             4 ; end / loop limit
             (choose s1 l1 r1 2) ; initial
             (lambda (s i) (/ s 2)) ; body of the loop
             )))
 

;; Synthesis problem
(define-syntax conds
  (syntax-rules ()
    [(conds a b c in) (and (eq? (join (body 0 a b) a b 0 0 0) (body 0 a b))
                             (eq? (join (body in a b) a b (body in b c) b c)
                                  (body in a c)))]))

(define cond1 (conds 2 7 9 0))
(define cond2 (conds 3 4 5 0))
(define cond3 (conds 5 12 30 0))

(define-symbolic n0 n1 n2 sum0 integer?)

;; (define odot 
;;   (time
;;    (synthesize
;;     #:forall '()
;;     #:guarantee (assert cond1))))

;; (printf "Sat: ~v\n" (sat? odot))
;; (if (unsat? odot) (printf "Core: ~v" (core odot)) 
;;     (begin (printf "Forms:\n") (print-forms odot)))
