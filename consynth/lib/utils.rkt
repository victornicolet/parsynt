#lang racket

(provide map-apply hash-set-pair!)

(define (map-apply func items)
  (if (list? items) (map func items) (func items)))

(define (hash-set-pair! hsh pair)
  (hash-set! hsh (car pair) (cdr pair)))
