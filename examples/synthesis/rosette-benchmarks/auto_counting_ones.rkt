#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic tmp i integer?)

(struct $ (f cnt aux_0))
(define ($-eq? s1 s2) (and (eq? ($-f s1) ($-f s2))
                           (eq? ($-cnt s1) ($-cnt s2))  (eq? ($-aux_0 s1) ($-aux_0 s2))
                           ))
;;Functional representation of the loop body.
(define (__loop_body__ s iL_ iR_)
  (Loop iL_ iR_ 10 s
        (lambda (__s i) (let ([f ($-f __s)] [cnt ($-cnt __s)]
                              [aux_0 ($-aux_0 __s)])
                          (let ([aux_0 (vector-ref a iL_)])
                            ($ (vector-ref a i)
                               (+ cnt (if (&& (vector-ref a i) (not f)) 1 0))
                               aux_0))))))

;;Wrapping for the sketch of the join.
(define (__join__ $L $R)
  (let ([f ($-f $L)] [cnt ($-cnt $L)] [aux_0 ($-aux_0 $L)] [x.f ($-f $R)]
        [x.cnt ($-cnt $R)] [x.aux_0 ($-aux_0 $R)])
    (let ([aux_0 (bExpr:boolean  f aux_0 x.f x.aux_0 1)])
      ($ (bExpr:boolean  f aux_0 x.f x.aux_0 1)
         (+ (bExpr:num->num  cnt x.cnt 1)
            (if (bExpr:boolean  f aux_0 x.f x.aux_0 1)
                (bExpr:num->num  cnt x.cnt 1) (bExpr:num->num  cnt x.cnt 1)))
         aux_0))))


;;Symbolic input state and synthesized id state
(define $_identity ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic aux_00 boolean?)
(define $_initial ($ #f 0 (choose 0 1 #t #f)))
;;Actual synthesis work happens here

(define odot (synthesize
              #:forall (list tmp i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
              #:guarantee
              (assert
               (and
                ($-eq?
                 (__loop_body__ $_initial 0 4)
                 (__join__
                  (__loop_body__ $_initial 0 2)
                  (__loop_body__ $_initial 2 4)))
                ($-eq?
                 (__loop_body__ $_initial 0 9)
                 (__join__
                  (__loop_body__ $_initial 0 3)
                  (__loop_body__ $_initial 3 9)))
                ($-eq?
                 (__loop_body__ $_initial 0 9)
                 (__join__
                  (__loop_body__ $_initial 0 7)
                  (__loop_body__ $_initial 7 9)))
                ($-eq?
                 (__loop_body__ $_initial 0 9)
                 (__join__
                  (__loop_body__ $_initial 0 4)
                  (__loop_body__ $_initial 4 9)))
                ($-eq?
                 (__loop_body__ $_initial 0 7)
                 (__join__
                  (__loop_body__ $_initial 0 5)
                  (__loop_body__ $_initial 5 7)))
                ($-eq?
                 (__loop_body__ $_initial 3 9)
                 (__join__
                  (__loop_body__ $_initial 3 6)
                  (__loop_body__ $_initial 6 9)))
                ($-eq?
                 (__loop_body__ $_initial 2 9)
                 (__join__
                  (__loop_body__ $_initial 2 7)
                  (__loop_body__ $_initial 7 9)))))))
