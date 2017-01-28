#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic tmp i n integer?)

(struct $ (match00))
(define ($-eq? s1 s2) (and (eq? ($-match00 s1) ($-match00 s2))
                           ))
;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_)
  (Loop i_begin_ i_end_ 10 s
        (lambda (__s i) (let ([match00 ($-match00 __s)])
                          ($ (|| (= i 1)
                                 (|| (= i (- 10 1))
                                     (&& match00 (not (vector-ref a i))))))))))

;;Wrapping for the sketch of the join.
(define (__join__ $L $R)
  (let ([match00 ($-match00 $L)] [x.match00 ($-match00 $R)])
    ($ (|| (bExpr:boolean   match00 x.match00  1)
           (|| (bExpr:boolean match00 x.match00 1)
               (bExpr:boolean  match00 x.match00 1))))))


;;Symbolic input state and synthesized id state
(define $_identity ($ (choose 0 1 #t #f)))
(define $_initial ($ #t))
;;Actual synthesis work happens here

(define odot (synthesize
              #:forall (list tmp i n    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
              #:guarantee (assert (and
                                   ($-eq? (__loop_body__ $_initial 0 4)
                                          (__join__ (__loop_body__ $_initial 0 2) (__loop_body__ $_initial 2 4)))
                                   ($-eq? (__loop_body__ $_initial 0 9)
                                          (__join__ (__loop_body__ $_initial 0 3) (__loop_body__ $_initial 3 9)))
                                   ($-eq? (__loop_body__ $_initial 0 9)
                                          (__join__ (__loop_body__ $_initial 0 7) (__loop_body__ $_initial 7 9)))
                                   ($-eq? (__loop_body__ $_initial 2 9)
                                          (__join__ (__loop_body__ $_initial 2 7) (__loop_body__ $_initial 7 9)))))))
