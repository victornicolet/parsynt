;; This is a test sketch for maximum top-left square example
#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)


(define-symbolic a b c integer?)


(define (foo in)
  (= (+ a b) (- c in)))


(define-symbolic x integer?)

(define odot
  (synthesize
   #:forall (list a b c)
   #:guarantee (assert (foo x))))

(print-forms odot)
