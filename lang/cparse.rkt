#lang racket

(require c)

(define (parse-file path) 
  (define input-file-port
    (open-input-file path))
  (parse-program input-file-port))



