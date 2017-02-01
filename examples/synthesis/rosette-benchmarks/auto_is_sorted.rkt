#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic tmp i integer?)

(struct $ (is_sorted___0 prev aux_0))
(define ($-eq? s1 s2) (and (eq? ($-is_sorted___0 s1) ($-is_sorted___0 s2))
                           (eq? ($-prev s1) ($-prev s2))  (eq? ($-aux_0 s1) ($-aux_0 s2))
                           ))
;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_)
  (Loop i_begin_ i_end_ 10 s
        (lambda (__s i) (let ([is_sorted___0 ($-is_sorted___0 __s)]
                              [prev ($-prev __s)] [aux_0 ($-aux_0 __s)])
                          (let ([aux_0 (vector-ref a i_begin_)])
                            ($ (&& is_sorted___0 (< prev (vector-ref a i))) (vector-ref a i)
                               aux_0))))))

;;Wrapping for the sketch of the join.
(define (__join__ $L $R)
  (let ([l.is_sorted___0 ($-is_sorted___0 $L)] [l.prev ($-prev $L)]
        [l.aux_0 ($-aux_0 $L)] [x.is_sorted___0 ($-is_sorted___0 $R)]
        [x.prev ($-prev $R)] [x.aux_0 ($-aux_0 $R)])
    (let ([aux_0 (bExpr:num->num l.aux_0 l.prev 1)])
      ($ (&& (bExpr:boolean l.is_sorted___0 x.is_sorted___0 1)
             ((BasicBinops:num->bool)
              (bExpr:num->num l.aux_0 x.aux_0 l.prev x.prev 1)
              (bExpr:num->num x.aux_0 x.prev 1)))
         (bExpr:num->num x.aux_0 x.prev 1) aux_0))))


;;Symbolic input state and synthesized id state
(define $_identity ($ (choose 0 1 #t #f #t) (choose 0 1 #t #f _min_int_) (choose 0 1 #t #f)))
(define-symbolic _min_int_ integer?)
(define $_initial ($ #t _min_int_ (choose 0 1 #t #f)))

(assert (and
         (> a$1 _min_int_)
         (> a$2 _min_int_)
         (> a$3 _min_int_)
         (> a$4 _min_int_)
         (> a$5 _min_int_)
         (> a$6 _min_int_)
         (> a$7 _min_int_)
         (> a$8 _min_int_)
         (> a$9 _min_int_)
         (> a$10 _min_int_)))
;;Actual synthesis work happens here

(define odot (synthesize
              #:forall (list tmp i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
              #:guarantee (assert (and
                                   ($-eq? (__loop_body__ $_initial 0 4)
                                          (__join__ (__loop_body__ $_initial 0 2)
                                                    (__loop_body__ $_initial 2 4)))
                                   ($-eq? (__loop_body__ $_initial 0 9)
                                          (__join__ (__loop_body__ $_initial 0 3) (__loop_body__ $_initial 3 9)))
                                   ($-eq? (__loop_body__ $_initial 0 9)
                                          (__join__ (__loop_body__ $_initial 0 7) (__loop_body__ $_initial 7 9)))
                                   ($-eq? (__loop_body__ $_initial 2 9)
                                          (__join__ (__loop_body__ $_initial 2 7) (__loop_body__ $_initial 7 9)))))))
