#lang racket

(provide map-apply)

(define (map-apply func items)
  (if (list? items) (map func items) (func items)))
