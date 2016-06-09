#lang racket

(provide (all-defined-out))

(define (map-apply func items)
  (if (list? items) (map func items) (func items)))

(define (hash-set-pair! hsh pair)
  (hash-set! hsh (car pair) (cdr pair)))

(define/contract (c-append l x)
  (-> (or/c list? any/c) any/c list?)
  (if (and (list? l) (not (empty? l)))
      (append l (list x))
      (list x)))

;; Increment/decrement statelike variables
(define-syntax-rule (pre-incr x) (begin (set! x (add1 x)) x))
(define-syntax-rule (post-incr x) (let ([xpre x]) (set! x (add1 x)) xpre))

(define xc 10)
