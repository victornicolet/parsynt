#lang racket

(require rosette/safe
         "../utils.rkt"
         (for-syntax "../utils.rkt"))

(provide (all-defined-out))

;; Macros generating symbolic definitions

(define-syntax-rule (Integers id ...) (define-symbolic id ... integer?))

(define-syntax-rule (Reals id ...) (define-symbolic id ... real?))

(define-syntax-rule (Booleans id ...) (define-symbolic id ... boolean?))

;; Read-only arrays are just functions from integers to another type
(define-syntax-rule (RoArray type (id ...))
  (define-symbolic id ... (~> integer? type)))

(define-syntax-rule (DefStruct vals ...)
  (struct state (vals ...)))

(define-syntax-rule (State s (vals ...))
  (define s (state vals ...)))

;; Macros generating function definitions body and join

(define-syntax-rule (LamBody (vnames ...) (b ...))
     (lambda (stt)
       (D-struct state stt (vnames ...)
                         (state b ...))))

(define-syntax-rule (LamJoin (vnames ...) (rnames ...) (b ...))
  (lambda (ll lr)
    (D-struct state ll (vnames ...)
                      (D-struct state lr (vnames ...) (rnames ...)
                      (state b ...)))))

(define-syntax (Synthesize stx)
  (syntax-rules ()
    [(Synthesize st1 st2 st0 (v ...))
     (synthesize
      #:forall (list v ...)
      #:guarantee (assert
                   (and (eq? (join st1 st0) st0)
                        (eq? (join st1 (body st2))
                             (body (join st1 st2))))))]))


;; Test macros
;; (struct state (a b c))
;; (define s0 (state 1 2 3))
;; (define s1 (state 3 3 4))

;; (Define-struct-eq state (a b c))

;; (Integers i1 i2 i3)
;; (assert (map integer? (list i1 i2 i3)))
;; (Reals r1 r2 r3)
;; (assert (map real? (list r1 r2 r3)))
;; (Booleans b1 b2 b3)
;; (assert (map boolean? (list b1 b2 b3)))
;; (RoArray integer? (a))
;; (assert (integer? (a i1)))
;; (define body (LamBody (a b c) ((+ a b) (+ 1 b) (add1 c))))
;; (define join (LamJoin (a b c) (x y z) ((+ a x) (+ b y) (+ c z))))
