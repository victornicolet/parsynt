#lang rosette/safe

(require consynth/lib/synthax/expressions)


(define-symbolic int_array (~> integer? integer?))
(define-symbolic bool_array (~> integer? boolean?))
(define-symbolic n n0 n1 n2 i integer?)
(define-symbolic b1 b2 boolean?)
;; Simple synthesis problems

;; Simplest example : array sum reduction
(define (join a b)
  (+ (Expr a b 2) (Expr a b 2)))

(define (body a i)
  (+ a (int_array i)))

;; (define odot 
;;  (time 
;;   (synthesize 
;;    #:forall (list n n0 i)
;;    #:guarantee (assert 
;;                 (and (eq? (join n 0) n)
;;                      (eq? (join n (body n0 i)) (body (join n n0) i)))))))


;; Dynamic last value : same operation (a sum reduction of an array) but the sum in the 
;; loop is guarded by a conditional.
;; The second element of the loop is set tp true whenever the variable is written in a loop
;; chunk, and the join adds the two values if the right-pair second element is set to true

(define (body2 a i)
  (if (bool_array i)
       (cons (+ (car a) (int_array i)) #t)
       a))

(define (join2 a b) 
  (let* 
      ([aa (car a)]
       [bb (car b)])
  (if (cdr b)
       (cons (Expr aa bb 2) #t)
       a)))

(define apr (cons n1 b1))
(define bpr (cons n2 b2))

 (define odot2
   (time
    (synthesize
     #:forall (list n1 n2 b1 b2 i)
     #:guarantee (assert 
                 (and (eq? (join2 apr (cons 0 #f)) apr)
                      (eq? (join2 apr (body2 bpr i))
                           (body2 (join2 apr bpr) i)))))))
