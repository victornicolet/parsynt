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

(define-struct (exn:frontc:unexpected exn:frontc) (type)
  #:extra-constructor-name make-exn:frontc:unexpected
  #:transparent)

(define (toplevel-exn src msg continuation-marks)
  (make-exn:frontc:toplevel 
   (format "~a -- Error at toplevel C analysis : ~a" (sprint-src src) msg)
   continuation-marks
   src ))

(define (unexpected-exn src type continuation-marks)
  (make-exn:frontc:unexpected
   (format "~a -- Unexpected ~a" (sprint-src src) type)
   continuation-marks))
