#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 integer?)
(define a (vector a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9))

(struct $ (iss prev aux_0))
(define ($-eq? s1 s2) (and (eq? ($-iss s1) ($-iss s2))
 (eq? ($-prev s1) ($-prev s2))  (eq? ($-aux_0 s1) ($-aux_0 s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_)
  (Loop i_begin_ i_end_ 10 s
    (lambda (__s i) (let ([iss ($-iss __s)] [prev ($-prev __s)]
      [aux_0 ($-aux_0 __s)])
      (let ([aux_0 (vector-ref a i_begin_)])
         ($ (&& iss (< prev (vector-ref a i))) (vector-ref a i) aux_0))))))

;;Wrapping for the sketch of the join.
(define (__join__ $L $R)
  (let ([l.iss ($-iss $L)] [l.prev ($-prev $L)] [l.aux_0 ($-aux_0 $L)]
    [x.iss ($-iss $R)] [x.prev ($-prev $R)] [x.aux_0 ($-aux_0 $R)])
    (let ([aux_0 (bExpr:num->num l.aux_0 l.prev 1)])
       ($ (&& (bExpr:boolean l.iss x.iss 1)
           ((BasicBinops:num->bool)
            (bExpr:num->num l.aux_0 x.aux_0 l.prev x.prev 1)
            (bExpr:num->num x.aux_0 x.prev 1)))
         (bExpr:num->num x.aux_0 x.prev 1) aux_0))))


;;Symbolic input state and synthesized id state
(define-symbolic __MIN_INT_ integer?)
(assert (and (> a$0 __MIN_INT_) (> a$1 __MIN_INT_) (> a$2 __MIN_INT_)
  (> a$3 __MIN_INT_) (> a$4 __MIN_INT_) (> a$5 __MIN_INT_) (> a$6 __MIN_INT_)
  (> a$7 __MIN_INT_) (> a$8 __MIN_INT_) (> a$9 __MIN_INT_)))
(define $_identity ($ (choose 0 1 #t #f #t) (choose 0 1 #t #f __MIN_INT_) (choose 0 1 #t #f)))
(define-symbolic aux_00 integer?)
(define $_initial ($ #t __MIN_INT_ (choose 0 1 #t #f)))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9)
  #:guarantee (assert (and
              ($-eq? (__loop_body__ $_initial 0 4)
                (__join__ (__loop_body__ $_initial 0 2) (__loop_body__ $_initial 2 4)))
              ($-eq? (__loop_body__ $_initial 0 9)
                (__join__ (__loop_body__ $_initial 0 3) (__loop_body__ $_initial 3 9)))
              ($-eq? (__loop_body__ $_initial 0 9)
                (__join__ (__loop_body__ $_initial 0 7) (__loop_body__ $_initial 7 9)))
              ($-eq? (__loop_body__ $_initial 2 9)
                (__join__ (__loop_body__ $_initial 2 7) (__loop_body__ $_initial 7 9)))))))
