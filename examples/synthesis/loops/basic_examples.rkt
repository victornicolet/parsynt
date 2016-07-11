#lang rosette/safe

(require consynth/lib/synthax/expressions
         consynth/lib/synthax/constructors
         "../utils.rkt")


(define-symbolic int_array (~> integer? integer?))
(define-symbolic bool_array (~> integer? boolean?))
(define-symbolic n n0 n1 n2 i integer?)
(define-symbolic b1 b2 boolean?)
;; Simple synthesis problems
(current-bitwidth #f)
;; Simplest example : array sum reduction
(define (join a b)
  (+ (Expr a b 2) (Expr a b 2)))

(define (body a i)
  (+ a (int_array i)))

(define (body-iters s0 from to)
  (Loop from to 10 s0 (lambda (s i) (body s i))))

(define odot
 (time
  (synthesize
   #:forall (list n n0 i int_array)
   #:guarantee (assert
                (and (eq? (join n 0) n)
                     (eq? (join n (body n0 i)) (body (join n n0) i)))))))

(print-if-sat odot)
;; Output :
;; cpu time: 137 real time: 239 gc time: 13
;; '(define (join a b) (+ b a))
(define s1 (body-iters 0 0 (- i 1)))
(define s2 (body-iters 0 i 9))
;; Testing another kind of verifcation conditions
(define odot-prim
 (time
  (synthesize
   #:forall (list n n0 i int_array)
   #:guarantee (assert
                (and (eq? (join n 0) n)
                     (eq? (join s1 (body s2 10)) (body (join s1 s2) 10)))))))

(print-if-sat odot-prim)
;; Ouput ;
;; Timeout

;; Dynamic last value : same operation (a sum reduction of an array) but the sum in the
;; loop is guarded by a conditional.
;; The second element of the loop is set tp true whenever the variable is written in a loop
;; chunk, and the join adds the two values if the right-pair second element is set to true

(define (body2 a i)
  (if (bool_array i)
      (cons (+ (car a) (int_array i)) #t)
      a))

(define (join2 a b)
  (let*
      ([aa (car a)]
       [bb (car b)])
    (if (cdr b)
        (cons (Expr aa bb 2) #t)
        a)))

(define apr (cons n1 b1))
(define bpr (cons n2 b2))
(define s0 (cons 0 #f))

(define odot2
  (time
   (synthesize
    #:forall (list n1 n2 b1 b2 i bool_array int_array)
    #:guarantee (assert
                 (and (eq? (join2 apr s0) apr)
                      (eq? (join2 apr (body2 bpr i))
                           (body2 (join2 apr bpr) i)))))))
