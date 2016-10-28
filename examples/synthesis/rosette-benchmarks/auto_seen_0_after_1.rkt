#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (seen_1 seen_0 res))

(define ($-eq? s1 s2) (and (eq? ($-seen_1 s1) ($-seen_1 s2))
 (eq? ($-res s1) ($-res s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
 (lambda (__s i)
(let ([seen_1 ($-seen_1 __s)]
      [res ($-res __s)])

  (let ([seen_1 (if (vector-ref a i) #t seen_1)])
    ($ seen_1
       (if (and seen_1 (not (vector-ref a i))) #t res)))))))

(define (__join__ $L $R)
(let
    ([seen_1-$L ($-seen_1 $L)]
     [res-$L ($-res $L)]
     [seen_1-$R ($-seen_1 $R)]
     [res-$R ($-res $R)])
  (let
      ([seen_1 (if (bExpr:boolean  seen_1-$L res-$L seen_1-$R res-$R 1)
                   (bExpr:boolean  seen_1-$L res-$L seen_1-$R res-$R 1)
                   (bExpr:boolean  seen_1-$L res-$L seen_1-$R res-$R 1))])
    ($ seen_1
       (if (bExpr:boolean  seen_1-$L res-$L seen_1-$R res-$R 1)
           (bExpr:boolean  seen_1-$L res-$L seen_1-$R res-$R 1)
           (bExpr:boolean  seen_1-$L res-$L seen_1-$R res-$R 1)))))
)

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define $initial ($ #f #f))
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
