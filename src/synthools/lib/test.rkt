#lang rosette

(require rosette/lib/synthax
         "./synthax/expressions.rkt"
         "./synthax/constructors.rkt")
(require rackunit)

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


(struct $-foo (s1 s2) #:transparent)

(define (test-loop-1 i0 iN)
  (LoopFunc i0 (lambda (i) (< i iN)) (lambda (i) (add1 i)) ($-foo 0 0)
            (lambda (s i) ($-foo (add1 ($-foo-s1 s)) (sub1 ($-foo-s2 s))))))

(define (test-loop-2 i0 iN)
  (Loop i0 iN 10 ($-foo 0 0)
            (lambda (s i) ($-foo (add1 ($-foo-s1 s)) (sub1 ($-foo-s2 s))))))


(check-eq? ($-foo-s1 (test-loop-1 0 10)) 10)
(check-eq? ($-foo-s2 (test-loop-1 0 10)) -10)
(check-eq? ($-foo-s2 (test-loop-1 5 10)) -5)
(check-eq? ($-foo-s1 (test-loop-1 5 10)) 5)
(check-equal? (test-loop-1 0 10) (test-loop-2 0 10))
