#lang rosette

(require rosette/lib/synthax racket/syntax)

(provide ScalarExpr LinearScalarExpr Expr)

;; Syntax for synthesizable expressions in holes

;; Available binary and unary operatorsn
(define-synthax BasicBinops
  ([(BasicBinops) (choose + -)]))

(define-synthax BinopsChoice
  ([(BinopsChoice) (choose + - * / expt)]))

(define-synthax BasicUnops
  ([(BasicUnops) (choose identity -)]))

(define-synthax UnopsChoice
  ([(UnopsChoixe) (choose identity - add1 sub1)]))

;; A scalar is a variable or a constant
(define-synthax Scalar
  ([(Scalar x ...) (choose x ... (??))]
   [(Scalar) (??)]))
;; and a scalar expression contains only scalars
(define-synthax (ScalarExpr x ... depth)
  #:base (Scalar x ...)
  #:else (choose
          ; Scalar
          (Scalar x ...)
          ; Binary expression
          ((BinopsChoice)
           (ScalarExpr x ... (sub1 depth))
           (ScalarExpr x ... (sub1 depth)))
          ; Unary expression
          ((UnopsChoice)
           (ScalarExpr x ... (sub1 depth)))
          ))

(define-synthax (LinearScalarExpr x ... depth)
  #:base (Scalar x ...)
  #:else (choose
          ; Scalar
          (Scalar x ...)
          ; Binary expression
          ((BasicBinops)
           (ScalarExpr x ... (sub1 depth))
           (ScalarExpr x ... (sub1 depth)))
          ; Unary expression
          ((BasicUnops)
           (ScalarExpr x ... (sub1 depth)))
          ))

;; WIP : vector expressions = arrays with subscripts
(define-synthax ArrayIndex 
  ([(ArrayIndex [a ...] x ... k) (Expr [a ...] x ... k)]
   [(ArrayIndex) (??)]))

(define-synthax ArrayCell
  ([(ArrayCell [a ...] [x ...] k) (vector-ref (Array a ...) (ArrayIndex [a ...] x... k))]
   [(ArrayCell [a ...] [x ...]) (vector-ref (Array a ...) (ScalarExpr x ... 2))]))

(define-synthax Array
  ([(Array a ...) (choose a ...)]))


(define-synthax (GenExpr [a ...] x ... depth)
  #:base (choose (Scalar x ...) (ArrayCell [a ...] [x ...]))
  #:else (choose 
          ; Binary expressions
          ((BinopsChoice)
           (GenExpr [a ...] [x ...] (sub1 depth))
           (GenExpr [a ...] [x ...] (sub1 depth))
          )
          ; UnaryExpressions
          ((UnopsChoice)
           (GenExpr [a ...] [x ...] (sub1 depth)))
          ; Scalars or ArrayCells
          (Scalar x ...) 
          (ArrayCell [a ...] [x ...])
  ))

;; Expression, containing Scalars and vectors 
;; General interface to place holes for expressions :
;; (Expr x1 x2 x3 2) generates scalar expressions of depth 2 possibly containing
;;                   variables x1 x2 x3.
;; (Expr [a1 a2] x1 x2 2) generate a general expression with scalars and array subscripts
;;                   containing array variables a1 a2 and scalar variables x1 x2.

(define-synthax Expr 
  ([(Expr [a ...] x ... depth) (GenExpr [a ...] x ... depth)]
   [(Expr x ... depth) (ScalarExpr x ... depth)]))


