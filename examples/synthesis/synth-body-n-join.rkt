#lang rosette

(require consynth/lib/synthax/expressions
         consynth/lib/synthax/constructors
         rosette/lib/synthax)

(define (array i) (* i i))

(define (pow2 i) (Loop 0 i 200 1 (lambda (s i) (* 2 s))))

(define (orig-body s0 l r)
  (Loop l ; start
        r ; end
        20; finitize --> no more than 20 iterations
        s0 ; inital value for the state
        (lambda (s i) (/ (+ s (array i)) 2)))) ; body of the loop

(define (synth-body s0 l r n)
  (Loop l r 20 s0
        (lambda (s i) 
          (let
              ([ai (array i)] [p2 (pow2 (- n i))])
            (+ (/ ai p2) s))))) ; Adding unknowns here leads easily to unsat

(define (join s1 l1 r1 s2 l2 r2)
  (+ s1 s2))
   ;; (LinearScalarExpr s2 l2 r2 2)
   ;; (LinearScalarExpr s1 l1 r1 2)))

;; (define a (synth-body 0 0 5 10))
;; (define b (synth-body 0 5 10 10))
;; (= (+ a b) (synth-body a 5 10 10)) ;--> #t
;; (= (+ a b) (orig-body 0 0 10)) ;--> #t

(define-syntax c_cond
  (syntax-rules ()
    [(c_cond sum0 id a b c)
     (let ([st1 (synth-body sum0 a b c)]
           [st2 (synth-body id b c c)])
       (and 
        ; Identity element is 0 from 0 to 0
        (= (join st1 a b 0 0 0) st1)
        ; Joining computation from a to b and b to c is like
        ; applying the body from b to c starting in the
        ; state after a to b
        (= (join st1 a b st2 b c)
           (synth-body st1 b c c))
        ;; The original body and the synthesized body give the
        ;; same result
        (= (synth-body sum0 a c c)
           (orig-body sum0 a c))))]))

;(define-symbolic a b c integer?)
(define-values (k m) (values 13 17))

(define odot
  (time
   (synthesize 
    #:forall (list k m);
    #:assume (and (<= k 0) (<= 0 m) (<= k 20) (<= m 20))
    #:guarantee (assert (and (c_cond 0 0 0 7 k)
                             (c_cond 0 0 0 5 m)
                             (c_cond 0 0 6 12 k)
                             (c_cond 0 0 0 2 m))))))



