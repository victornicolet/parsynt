#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))


(struct $ (pos mts aux_1))
(define ($-eq? s1 s2) (and (eq? ($-pos s1) ($-pos s2))
                           (eq? ($-mts s1) ($-mts s2))
                           (eq? ($-aux_1 s1) ($-aux_1 s2))
                           ))
;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_)
  (Loop i_begin_ i_end_ 10 s
        (lambda (__s i) (let ([pos ($-pos __s)] [mts ($-mts __s)]
                              [aux_1 ($-aux_1 __s)])
                          (let ([aux_1 (+ (vector-ref a i) aux_1)])
                            ($ (if (= mts 0) i pos) (max 0 (+ mts (vector-ref a i))) aux_1))))))

;;Wrapping for the sketch of the join.
(define (__join__ $L $R)
  (let ([l.pos ($-pos $L)] [l.mts ($-mts $L)] [l.aux_1 ($-aux_1 $L)]
        [x.pos ($-pos $R)] [x.mts ($-mts $R)] [x.aux_1 ($-aux_1 $R)])
    (let ([aux_1 (+ ;; (bExpr:num->num x.pos x.mts
                  x.aux_1 ;; 1
                  ;; )
                  ;; (bExpr:num->num l.pos l.mts
                  l.aux_1 ;; x.pos x.mts x.aux_1 1)
                  )])
      ($ (if (> (+ l.mts x.aux_1) x.mts) l.pos x.pos)
         (max x.mts
              (+ l.mts x.aux_1)) aux_1))))


;;Symbolic input state and synthesized id state
(define $_identity ($ -1 0 0))

(define $_initial ($ -1 0 0))
;;Actual synthesis work happens here

(define odot (synthesize
              #:forall (list  a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
              #:guarantee (assert (and
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
