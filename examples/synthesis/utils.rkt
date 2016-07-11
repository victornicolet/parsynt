#lang rosette/safe

(require rosette/lib/synthax)

(provide PolytopeLU get-synthax
         ArithOp ArithExpr)
;; Generates the assertions for a polytope P such that each  a < u and a <=
;; (PolytopeLU [lower bounds ..] [indexes ... ] [upper bounds ...])
(define-syntax PolytopeLU
  (syntax-rules ()
    [(PolytopeLU [l ...] [a ...] [u ...]) 
     (assert (and (and (< a u) (<= l a)) ...)) ]))

(define (get-synthax synthesis-solution) 
  (car synthesis-solution))

;; Synthesizable arithmetic expressions, based onyl on Rosette symbolic values
;; ArithExpr c ... can synthesize any arithmetic expression involving ArithOp
;; binary operators, and constants and identifiers in c...

(define-synthax ArithOp
  ([(ArithOp) (choose + * - /)]))

(define-synthax (ArithExpr c ... depth)
  #:base (choose c ... (??))
  #:else (choose
          ;; Scalar value
          (c ... (??))
          ;; Binary operator 
          ((ArithOp)
           (ArithExpr c ... (??) (sub1 depth))
           (ArithExpr c ... (??) (sub1 depth)))))

;; For pairs
(define fst car)
(define snd cadr)
