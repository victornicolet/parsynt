#lang racket

(require c
         "./pprint.rkt")

(provide (all-defined-out))

(define-struct (exn:frontc exn) (src)
  #:extra-constructor-name make-exn:frontc
  #:transparent)

(define-struct (exn:frontc:toplevel exn:frontc) ()
  #:extra-constructor-name make-exn:frontc:toplevel
  #:transparent)

(define (toplevel-exn src msg continuation-marks)
  (make-exn:frontc:toplevel 
   (format "~a -- Error at toplevel C analysis : ~a" (sprint-src src) msg)
   continuation-marks
   src ))
