#lang rosette

(require rosette/lib/synthax
         "../utils.rkt")

(define-synthax (MultE i ... k)
  #:base (choose i ... (??))
  #:else (choose i ... (??)
                 (* (choose i ... (??)) (MultE i ... (sub1 k)))))

(define-synthax (AddE [dep] i ... k)
  #:base (MultE i ... dep)
  #:else (choose (MultE i ... dep)
                (+ (MultE i ... dep) (AddE [dep] i ... (sub1 k)))))

(current-bitwidth 5)
;; (SA) Simple affine array access pattern
(define (SA-LMAD i c)
  (AddE [3] i c 4))

(define-symbolic i1 a integer?)

(define example-sa
  (time
   (synthesize 
    #:forall (list i1 a)
    #:guarantee (assert (eq? (- (+ i1 (* i1 3)) 4)
                             (SA-LMAD i1 a))))))
;; time : cpu time: 81 real time: 279 gc time: 12
;; result : '(define (SA-LMAD i c) (+ (* 4 1) (+ (* 4 i) -8)))

;; (MLI) Multi-index linear subscripts
(define (MLI-LMAD i j k l)
  (AddE [3] i j k l 4))

(define-symbolic i2 c1 c2 integer?)

(define example-mli
  (time
   (synthesize
    #:forall (list i1 i2 c1 c2)
    #:guarantee (assert
                 (eq? 
                  (+ i1 (- i2 3) 4)
                  (MLI-LMAD i1 i2 c1 c2))))))
;; time : cpu time: 97 real time: 399 gc time: 0
;; result : '(define (MLI-LMAD i j k l) (+ i (+ 1 j)))

;; (CS) Coupled subscripts: in the array access, two different dimensions 
;; are acessed with only one index. In the linear representation, the
;; index is mutlitplied by the row-size
(define (CS-LMAD i k l)
  (AddE [3] i k l 4))

(define example-cs
  (time
   (synthesize
    #:forall (list i1 c1 c2)
    #:guarantee (assert
                 (eq? 
                  (+ (* i1 c1) (- i1 3) 4)
                  (CS-LMAD i1 c1 c2))))))
;; time : cpu time: 134 real time: 2645 gc time: 0
;; result : '(define (CS-LMAD i k l) (+ i (+ 1 (* 1 (* i k)))))

;; (NA) Non-affine subscripts
(define (NA-LMAD i j k l)
  (AddE [3] i j k l 3))

(define example-na
  (time
   (synthesize
    #:forall (list i1 i2 c1 c2)
    #:guarantee (assert (eq? (+ (* i1 (+ i1 3)) i2 c2)
                             (NA-LMAD i1 i2 c1 c2))))))
;; time : cpu time: 116 real time: 2076 gc time: 0
;; result : '(define (NA-LMAD i j k l) (+ l (+ j (+ (* i i) (* 3 i)))))
