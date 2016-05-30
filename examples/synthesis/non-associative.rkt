#lang rosette

(require consynth/lib/synthax/expressions)

(define-symbolic int_array (~> integer? integer?))
(define-symbolic a b i0 i1 i2 integer?)

(struct state (sum to from))

(define (body s to from)
  (state
   (for/fold ([sum (state-sum s)])
             ([i (in-range from to)])
     (values (/ (+ sum (int_array i)) 2)))
   to from))

(define (join lft rgt)
  (let
      ([ato (state-to lft)]
    [bto (state-to rgt)]
    [afrom (state-from lft)]
    [bfrom (state-from rgt)]
    [a (state-sum lft)]
    [b (state-sum rgt)])
  (+ (Expr a afrom ato 2) (Expr b bfrom bto 2))))

(define st1 (state a 0 0))
(define st2 (state b 0 0))
(define stid (state 0 0 0))

(define odot 
  (time
   (synthesize
    #:forall (list a b i0 i1 i2)
    #:guarantee (assert (and (eq? (join st1 stid) st1)
                             (eq? (join st1 (body st2 i1 i2))
                                  (body (join st1 st2) i1 i2)))))))
