#lang rosette

(require rosette/lib/synthax racket/syntax)

(provide ScalarExpr LinearScalarExpr bExpr
         ;; Numeral to numeral expressions
         NumExprArith NumExprNL NumExprBasic
         ;; Comparisons
         BoolExprCompar
         ;; Boolean only expressions
         BoolExpr
         ;; If-then-else forms of numeral type
         NumIte
         ;; Unused for now
         ComparisonOps)

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

(define-synthax ArithBinops
  ([(ArithBinops 0) (choose + -)]))

(define-synthax BasicBinopsNum
  ([(BasicBinopsNum 0) (choose + - min max)]))

(define-synthax NLBinopsNum
  ([(NLBinopsNum 0) (choose * / + - min max)]))

(define-synthax BasicUnopsNum
  ([(BasicUnopsNum 0) (choose add1 sub1)]))

(define-synthax ComparisonOps
  ([(ComparisonOps 0) (choose > >= =)]))


(define-synthax BinopsBool
  ([(BinopsBool 0) (choose && ||)]))


(define-synthax BasicUnopsBool
  ([(BasicUnopsBool 0) (choose ! identity)]))

(define-synthax (NumExprArith x ... depth)
  #:base (Scalar x ...)
  #:else (choose
          (Scalar x ...)
          ; Binary expression
          ((ArithBinops 0)
           (NumExprArith x ... (sub1 depth))
           (NumExprArith x ... (sub1 depth)))
          ; Unary expression
          ((BasicUnopsNum 0)
           (NumExprArith x ... (sub1 depth)))))

(define-synthax (NumExprBasic x ... depth)
  #:base (Scalar x ...)
  #:else (choose
          (Scalar x ...)
          ; Binary expression
          ((BasicBinopsNum 0)
           (NumExprBasic x ... (sub1 depth))
           (NumExprBasic x ... (sub1 depth)))
          ; Unary expression
          ((BasicUnopsNum 0)
           (NumExprBasic x ... (sub1 depth)))))

(define-synthax (NumExprNL x ... depth)
  #:base (Scalar x ...)
  #:else (choose
          (Scalar x ...)
          ; Binary expression
          ((NLBinopsNum 0)
           (NumExprBasic x ... (sub1 depth))
           (NumExprBasic x ... (sub1 depth)))
          ; Unary expression
          ((BasicUnopsNum 0)
           (NumExprBasic x ... (sub1 depth)))))


(define-synthax BoolExprCompar
  ([(BoolExprCompar x ... d) (choose
                               ((BasicUnopsBool 0)
                               ((ComparisonOps 0)
                                (NumExprBasic x ... 1)
                                (NumExprBasic x ... 1)))
                               ((ComparisonOps 0)
                                (NumExprBasic x ... 1)
                                (NumExprBasic x ... 1)))]))

(define-synthax (BoolExpr x ... depth)
  #:base (Scalar x ...)
  #:else (choose #t #f
          (Scalar x ...)
          ((BasicUnopsBool 0)
           (BoolExpr x ... (sub1 depth)))
          ((BinopsBool 0)
           (BoolExpr x ... (sub1 depth))
           (BoolExpr x ... (sub1 depth)))))


(define-synthax NumIte
  ([(NumIte (r ...) (b ...) d) (if
                                  (choose
                                   b ...
                                   (BoolExprCompar r ... d)
                                   (BoolExpr b ... d))
                                  (NumExprBasic r ... d)
                                  (NumExprBasic r ... d))]))
