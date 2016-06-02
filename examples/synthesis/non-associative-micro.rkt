#lang rosette/safe

(require consynth/lib/synthax/expressions
         consynth/lib/synthax/constructors
         rosette/lib/synthax)

(define-symbolic int_array (~> integer? real?))

(define recursion-limit 4)


(define (f i) (* i i))

(define (body sum from to)
  (Loop from to recursion-limit sum (lambda (s i) (/ (+ s (f i)) 2))))

(define (join s1 l1 r1 s2 l2 r2)
  (+ (Expr s2 l2 r2 1)
     (letrec 
         ([aux (lambda (s i) 
                 (if (or (>= i (choose r1 r2)) (>= i recursion-limit))
                     s 
                     (aux (/ s 2) i)))])
       (aux (choose s1 s2) (choose l1 l2)))
     ))
 

;; Synthesis problem
(define-syntax conds
  (syntax-rules ()
    [(conds a b c) (let ([st1 (body 0 a b)] [st2 (body 0 b c)])
                     (and (eq? (join st1 a b 0 0 0) st1)
                          (eq? (join st1 a b st2 b c)
                               (body 0 a c))))]))


(define-symbolic n0 n1 n2 sum0 integer?)
(assert (and (<= 0 n0) (<= n0 n1) (<= n0 recursion-limit) (<= n1 n2) (<= n2 recursion-limit)))


;; (define odot 
;;   (time
;;    (synthesize
;;     #:forall (list n0 n1 n2)
;;     #:guarantee (assert (conds n0 n1 n2)))))

;; (printf "Sat: ~v\n" (sat? odot))
;; (if (unsat? odot) (printf "Core: ~v" (core odot)) 
;;     (begin (printf "Forms:\n") (print-forms odot)))
