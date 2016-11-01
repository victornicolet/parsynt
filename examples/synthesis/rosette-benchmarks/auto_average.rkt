#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i n integer?)

(struct $ (average___0))
(define ($-eq? s1 s2) (and (eq? ($-average___0 s1) ($-average___0 s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
       (lambda (__s i)
         (let
             ([average___0 ($-average___0 __s)])
           ($ (+ average___0 (/ (vector-ref a i) n)))))))

(define (__join__ $L $R)
(let
    ([average___0-$L ($-average___0 $L)]
     [average___0-$R ($-average___0 $R)])
  ($ (+ (bExpr:num->num  average___0-$L average___0-$R 1)
        (bExpr:num->num  average___0-$L average___0-$R 1))))
)

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f)))
(define $initial ($ 0))
;;Actual synthesis work happens here

(define odot
(synthesize
#:forall (list i n a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
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
