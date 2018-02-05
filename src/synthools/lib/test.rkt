#lang rosette

(require rosette/lib/synthax
         "./synthax/expressions.rkt"
         "./synthax/constructors.rkt")


(define-symbolic a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 s0 integer?)
(define a (vector a0 a1 a2 a3 a4 a5 a6 a7 a8 a9))


(define (fsum _0 _N c)
  (Loop _0 _N 10 c (lambda (s i) (+ (vector-ref a i) s))))


(define (fsumbdy s i)
  (let ([ai (vector-ref a i)])
    (NumExprBasic s ai 1)))

(define (fsum? _0 _N c)
  (Loop _0 _N 10 c fsumbdy))

(define odot
  (synthesize
   #:forall (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 s0)
   #:guarantee (assert (= (fsum 0 9 s0) (fsum? 0 9 s0)))))
