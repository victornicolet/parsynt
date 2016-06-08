#lang racket

(provide map-apply hash-set-pair! c-append)

(define (map-apply func items)
  (if (list? items) (map func items) (func items)))

(define (hash-set-pair! hsh pair)
  (hash-set! hsh (car pair) (cdr pair)))

(define (c-append l x) 
  (if (list? l) (append l x) (list x)))
