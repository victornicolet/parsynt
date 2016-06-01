#lang rosette/safe

(require consynth/lib/synthax/expressions
         rosette/lib/synthax)

(define-symbolic int_array (~> integer? real?))
(define-symbolic a b integer?)

(define (f i) (* i i))

(define (body sum from to)
  (letrec ([aux (lambda (s i to) (if (>= i to) 
                                        s
                                        (aux (/ (+ s (f i)) 2) (add1 i) to)) )])
    (aux sum from to)))

(define (join s1 l1 r1 s2 l2 r2)
  (letrec ([aux (lambda (s i to) (if (>= i to)
                                     s
                                     (aux (/ s  2) (add1 i) to)))])
    (+ (aux (LinearScalarExpr s1 l1 r1 2) (choose l1 r1 l2 r2) (choose l1 r1 l2 r2))
       (Expr s2 r2 l2 1))))
 

;; Synthesis problem
(define i0 0)
(define i1 2)
(define i2 4)
(define-syntax conds
  (syntax-rules ()
    [(conds a b c) (and (eq? (join (body 0 a b) a b 0 0 0) (body 0 a b))
                             (eq? (join (body 0 a b) a b (body 0 b c) b c)
                                  (body 0 a c)))]))

(define cond1 (conds i0 i1 i2))
(define cond2 (conds 3 4 5))

(define odot 
  (time
   (synthesize
    #:forall (list int_array)
    #:guarantee (assert (and cond1 cond2)))))

(printf "Sat: ~v\n" (sat? odot))
(if (unsat? odot) (printf "Core: ~v" (core odot)) 
    (begin (printf "Forms:\n") (print-forms odot)))
