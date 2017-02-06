#lang rosette

(require rosette/lib/synthax racket/syntax)

(provide ScalarExpr LinearScalarExpr bExpr
         ;; Numeral to numeral expressions
         bExprArith:num->num bExprNL:num->num bExpr:num->num
         ;; Comparisons
         bExpr:num->bool
         ;; Boolean only expressions
         bExpr:boolean
         ;; If-then-else forms of numeral type
         bExpr:ternary->num
         ;; Unused for now
         BasicBinops:num->bool)

;; Syntax for synthesizable expressions in holes

;; Available binary and unary operatorsn
(define-synthax BasicBinops
  ([(BasicBinops) (choose + -)]))

(define-synthax BinopsChoice
  ([(BinopsChoice) (choose + - * / expt)]))

(define-synthax BasicUnops
  ([(BasicUnops) (choose identity -)]))

(define-synthax UnopsChoice
  ([(UnopsChoice) (choose identity - add1 sub1)]))

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

(define-synthax bExpr
  ([(bExpr [a ...] x ... depth) (GenExpr [a ...] x ... depth)]
   [(bExpr x ... depth) (ScalarExpr x ... depth)]))


;; Type-specific expressions

;; Numeral to numerals : complexity increasing from airthmetic-only,
;; to expressions with min/max and then adding non-linear operators

(define-synthax ArithBinops:num->num
  ([(ArithBinops:num->num) (choose + -)]))

(define-synthax BasicBinops:num->num
  ([(BasicBinops:num->num) (choose + - min max)]))

(define-synthax NonLinearBinops:num->num
  ([(NonLinearBinops:num->num) (choose * / + - min max)]))

(define-synthax BasicUnops:num->num
  ([(BasicUnops:num->num) (choose add1 sub1)]))

(define-synthax BasicBinops:num->bool
  ([(BasicBinops:num->bool) (choose > >= =)]))


(define-synthax BasicBinops:bool->bool
  ([(BasicBinops:bool->bool) (choose && ||)]))


(define-synthax BasicUnops:bool
  ([(BasicUnops:bool) (choose ! identity)]))

(define-synthax (bExprArith:num->num x ... depth)
  #:base (Scalar x ...)
  #:else (choose
          (Scalar x ...)
          ; Binary expression
          ((ArithBinops:num->num)
           (bExpr:num->num x ... (sub1 depth))
           (bExpr:num->num x ... (sub1 depth)))
          ; Unary expression
          ((BasicUnops:num->num)
           (bExpr:num->num x ... (sub1 depth)))))

(define-synthax (bExpr:num->num x ... depth)
  #:base (Scalar x ...)
  #:else (choose
          (Scalar x ...)
          ; Binary expression
          ((BasicBinops:num->num)
           (bExpr:num->num x ... (sub1 depth))
           (bExpr:num->num x ... (sub1 depth)))
          ; Unary expression
          ((BasicUnops:num->num)
           (bExpr:num->num x ... (sub1 depth)))))

(define-synthax (bExprNL:num->num x ... depth)
  #:base (Scalar x ...)
  #:else (choose
          (Scalar x ...)
          ; Binary expression
          ((NonLinearBinops:num->num)
           (bExpr:num->num x ... (sub1 depth))
           (bExpr:num->num x ... (sub1 depth)))
          ; Unary expression
          ((BasicUnops:num->num)
           (bExpr:num->num x ... (sub1 depth)))))


(define-synthax bExpr:num->bool
  ([(bExpr:num->bool x ... d) (choose
                               ((BasicUnops:bool)
                               ((BasicBinops:num->bool)
                                (bExpr:num->num x ... 1)
                                (bExpr:num->num x ... 1)))
                               ((BasicBinops:num->bool)
                                (bExpr:num->num x ... 1)
                                (bExpr:num->num x ... 1)))]))

(define-synthax (bExpr:boolean x ... depth)
  #:base (Scalar x ...)
  #:else (choose #t #f
          (Scalar x ...)
          ((BasicUnops:bool)
           (bExpr:boolean x ... (sub1 depth)))
          ((BasicBinops:bool->bool)
           (bExpr:boolean x ... (sub1 depth))
           (bExpr:boolean x ... (sub1 depth)))))


(define-synthax bExpr:ternary->num
  ([(bExpr:ternary->num (r ...) (b ...) d) (if
                                  (choose
                                   b ...
                                   (bExpr:num->bool r ... d)
                                   (bExpr:boolean b ... d))
                                  (bExpr:num->num r ... d)
                                  (bExpr:num->num r ... d))]))
