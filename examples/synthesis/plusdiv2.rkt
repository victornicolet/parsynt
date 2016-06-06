#lang rosette/safe

(require 
 rosette/lib/synthax
 consynth/lib/synthax/constructors
 consynth/lib/synthax/expressions)

(define max-iters 20)
(define max-pow 200)
(current-bitwidth #f)

(define (array i) (* i i))
(define (pow2 i) 
  (Loop 0 i max-pow 1 (lambda (s i) (* s 2))))

;; Forward computation
(define (orig-body b n)
  (Loop 0 b max-iters 0 (lambda (s i) (/ (+ s (array i)) 2))))

;; Backwards
(define (back-body b n) 
   (Loopsc 0 b max-iters (cons 0 2) 
         (lambda (s i) 
           (let ([c (cdr s)][a (car s)])
           (cons 
            (+ a (
                  /
                  (array (- n (+ i 1))) 
                  (choose i c n 1))) ; s = s + a[n-i] / c
            ((choose + / * -) c 2)))))) ; c = 2 * c

;; "Two-way" body
(define (synth-body b n)
  (Loop 0 b max-iters 0 (lambda (s i) (Expr s (/ (array i) (pow2 (- n i))) 2))))

(define-syntax c_cond 
  (syntax-rules ()
    [(c_cond b n) (eq? (orig-body b n) (car (back-body b n)))]))

(define-symbolic a integer?)
(assert (and (<= 0 a) (<= a max-iters)))

 (define odot
   (synthesize 
    #:forall (list a)
    #:guarantee (assert (c_cond a a))))

(print-forms odot)
