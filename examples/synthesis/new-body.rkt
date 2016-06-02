#lang rosette

(require 
 rosette/lib/synthax
 consynth/lib/synthax/constructors
 consynth/lib/synthax/expressions)

(define max-iters 20)

(define (array i) (* i i))
(define (pow2 i) 
  (Loopsc 0 i max-iters 1 (lambda (s i) (* s 2))))

(define (orig-body s0 b)
  (Loopsc 0 b max-iters s0 (lambda (s i) (/ (+ s (array i)) 2))))

(define (synth-body s0 b)
  (Loopsc 0 b max-iters s0 (lambda (s i) (+ s (/ (array i) (pow2 (- b i)))))))

(define-syntax c_cond 
  (syntax-rules ()
    [(c_cond s0 b) (eq? (orig-body s0 b) (synth-body s0 b))]))

(define-symbolic a integer?)
(assert (and (< 0 a) (<= a max-iters)))

(define odot
  (synthesize 
   #:forall (list a)
   #:guarantee (assert (c_cond 0 a))))

;(print-forms odot)
