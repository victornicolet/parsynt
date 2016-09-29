#lang rosette

(require consynth/lib rosette/lib/synthax)

(current-bitwidth #f)

(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

;;Actual synthesis work happens here

(define e (vector-ref a i))
(define fe (+ (vector-ref a  i) (vector-ref a (+ i 1))))

(define (f x) (bExpr:num->num (vector-ref a (+ i 1)) x 2))

(define odot
  (synthesize
   #:forall (list i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
   #:guarantee (assert (eq? fe (f e)))))


(define e2 (+ (vector-ref a  i) (vector-ref a (+ i 1))))
(define fe2 (+ (vector-ref a  i) (+ (vector-ref a (+ i 1))
                                    (vector-ref a (+ (+ i 1) 1)))))

(define (f2 x) (bExpr:num->num (vector-ref a (+ (+ i 1) 1)) x 2))

(define odot2
  (synthesize
   #:forall (list i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
   #:guarantee (assert (eq? fe2 (f2 e2)))))
