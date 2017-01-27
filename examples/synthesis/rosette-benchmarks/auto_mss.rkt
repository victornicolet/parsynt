#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (mts mss aux_1 aux_3))
(define ($-eq? s1 s2) (and (eq? ($-mts s1) ($-mts s2))
                           (eq? ($-mss s1) ($-mss s2))  (eq? ($-aux_1 s1) ($-aux_1 s2))
                           (eq? ($-aux_3 s1) ($-aux_3 s2))
                           ))
;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_)
  (Loop i_begin_ i_end_ 10 s
        (lambda (__s i) (let ([mts ($-mts __s)] [mss ($-mss __s)]
                              [aux_1 ($-aux_1 __s)] [aux_3 ($-aux_3 __s)])
                          (let ([aux_1 (+ (vector-ref a i) aux_1)])
                            (let ([mts (max 0 (+ mts (vector-ref a i)))]
                                  [mss (max mss (+ mts (vector-ref a i)))])
                              ($ mts mss aux_1 (max aux_1 aux_3))))))))

;;Wrapping for the sketch of the join.
(define (__join__ $L $R)
  (let ([mts ($-mts $L)] [mss ($-mss $L)] [aux_1 ($-aux_1 $L)]
        [aux_3 ($-aux_3 $L)] [x.mts ($-mts $R)] [x.mss ($-mss $R)]
        [x.aux_1 ($-aux_1 $R)] [x.aux_3 ($-aux_3 $R)])
    (let ([raux_1 (+ aux_1 x.aux_1)])
      (let ([rmts (max (+ mts x.aux_1) x.mts)]
            [rmss (max
                   (bExpr:num->num  mts mss aux_1 aux_3 1)
                   (bExpr:num->num  mts mss aux_1 aux_3
                                    x.mts x.mss x.aux_1 x.aux_3 1))])
        ($ rmts rmss raux_1
           (max
            (bExpr:num->num  mts mss aux_1 aux_3 x.mts x.mss x.aux_1 x.aux_3 1)
            (bExpr:num->num  mts mss aux_1 aux_3 x.mts x.mss x.aux_1 x.aux_3 1)))))))


;;Symbolic input state and synthesized id state
(define $_identity ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic aux_30 aux_10 integer?)
(define $_initial ($ 0 0 0 0))
;;Actual synthesis work happens here

(define odot (synthesize
              #:forall (list i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)#:guarantee
              (assert (and
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
                        (__loop_body__ $_initial 2 9)
                        (__join__
                         (__loop_body__ $_initial 2 7)
                         (__loop_body__ $_initial 7 9)))))))
