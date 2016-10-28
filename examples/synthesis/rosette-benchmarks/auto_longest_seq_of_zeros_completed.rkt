#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (cur_length max_length))
(define ($-eq? s1 s2) (and (eq? ($-cur_length s1) ($-cur_length s2))
 (eq? ($-max_length s1) ($-max_length s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
 (lambda (__s i)
(let ([cur_length ($-cur_length __s)]
  [max_length ($-max_length __s)]) ($ (if (vector-ref a i) (+ cur_length 1)
                                        0)
                                   (max max_length (if (vector-ref a i)
                                     (+ cur_length 1) 0)))))))
(define (__join__ $L $R)
(let
 ([cur_length-$L ($-cur_length $L)] [max_length-$L ($-max_length $L)]
  [cur_length-$R ($-cur_length $R)] [max_length-$R ($-max_length $R)])
 ($ (if (bExpr:num->bool cur_length-$L max_length-$L cur_length-$R max_length-$R 1)
        (bExpr:num->num cur_length-$L max_length-$L cur_length-$R max_length-$R 1)
        (bExpr:num->num  cur_length-$L max_length-$L cur_length-$R max_length-$R 1))
    (max (bExpr:num->num  cur_length-$L max_length-$L cur_length-$R max_length-$R 1)
         (if
          (bExpr:num->bool cur_length-$L max_length-$L cur_length-$R max_length-$R 1)
          (bExpr:num->num  cur_length-$L max_length-$L cur_length-$R max_length-$R 1)
          (bExpr:num->num  cur_length-$L max_length-$L cur_length-$R max_length-$R 1)))))
)

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define $initial ($ 0 0))
;;Actual synthesis work happens here

(define odot
(synthesize
#:forall (list i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
#:guarantee (assert
(and
 ($-eq?
 (__loop_body__ $initial 0 4)
(__join__  (__loop_body__ $initial 0 2)  (__loop_body__ $_init 2 4)))

($-eq?
 (__loop_body__ $initial 0 9)
(__join__  (__loop_body__ $initial 0 3)  (__loop_body__ $_init 3 9)))

($-eq?
 (__loop_body__ $initial 0 9)
(__join__  (__loop_body__ $initial 0 7)  (__loop_body__ $_init 7 9)))

($-eq?
 (__loop_body__ $initial 0 9)
(__join__  (__loop_body__ $initial 0 4)  (__loop_body__ $_init 4 9)))

($-eq?
 (__loop_body__ $initial 0 7)
(__join__  (__loop_body__ $initial 0 5)  (__loop_body__ $_init 5 7)))

($-eq?
 (__loop_body__ $initial 3 9)
(__join__  (__loop_body__ $initial 3 6)  (__loop_body__ $_init 6 9)))

($-eq?
 (__loop_body__ $initial 2 9)
(__join__  (__loop_body__ $initial 2 7)  (__loop_body__ $_init 7 9)))
))
))