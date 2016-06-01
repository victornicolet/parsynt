#lang rosette

;; This example causes Rosette to loop and use more and more memory.
;; However the same example with a restricted set of choices (only
;; two choices instead of 4) works perfeclty, and the synthesis takes
;; less than a second.

(require rosette/lib/synthax)

(define (body l1 l2 r1 r2)
  (letrec ([aux (lambda (s i) (if (>= i (choose r1 r2 l1 l2))
                                 s
                                 (aux (+ s 1) (add1 i))))])
    (= (aux 0 (choose r1 r2 l1 l2)) (- r2 l2))))


(define a 1)
(define b 2)
(define c 3)
(define d 4)


(define odot
  (time
   (synthesize
    #:forall '()
    #:guarantee (assert (body a b c d)))))

(if (unsat? odot) (core odot) (print-forms odot) )
