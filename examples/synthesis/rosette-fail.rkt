#lang rosette

;; This example causes Rosette to loop and use more and more memory.
;; However the same example with a restricted set of choices (only
;; two choices instead of 4) works perfeclty, and the synthesis takes
;; less than a second.
;; The examples work with the following solutions :
;; - Instead of using the four choices, use only two, with one of 
;;   them being the actual "good" choice. 
;; - Add a second condition in the loop, causing the loop to terminate
;;   if it reaches a fixed number of iterations
;;     (if (or (>= i (choose l1 l2 r1 r2)) (>= i 10))


(require rosette/lib/synthax)

(define dum1 4)
(define dum2 20)
(define dum3 2)

(define (body l1 l2 r1 r2)
  (letrec ([aux (lambda (s i) (if (>= i (choose l1 l2 r1 r2))
                                 s
                                 (aux (+ s 1) (add1 i))))])
    (= (aux 0 (choose l1 l2)) (- r2 l2))))


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

;; In this example, the probalem is not the termination of the loop 
;; anymore but the symbolic start index. Giving a symbolic start index 
;; to this form of loops causes the loop to never terminate.

(define (body s0 start end)
  (letrec 
      ([aux (lambda (s i) (if (or (<= end i) (<= 10 i)) s (aux s (add1 i))))])
    (aux s0 start)))

(define-symbolic a b integer?)
(assert (and (<= 0 a) (<= a b) (<= b 10)))

(body 1 0 b) ; terminates
(body 1 a b) ; doesn't terminate
