#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic ar$1 ar$2 ar$3 ar$4 ar$5 ar$6 ar$7 ar$8 ar$9 ar$10 integer?)
(define ar (vector ar$1 ar$2 ar$3 ar$4 ar$5 ar$6 ar$7 ar$8 ar$9 ar$10))
(define-symbolic tmp___0 tmp i b a integer?)

(struct $ (an bn aux_1))
(define ($-eq? s1 s2) (and (eq? ($-an s1) ($-an s2))
 (eq? ($-bn s1) ($-bn s2))  (eq? ($-aux_1 s1) ($-aux_1 s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s iL_ iR_)
  (Loop iL_ iR_ 10 s
    (lambda (__s i) (let ([an ($-an __s)] [bn ($-bn __s)]
      [aux_1 ($-aux_1 __s)])
      (let ([aux_1 (= (vector-ref ar iL_) a)])
         ($ (&& (= (vector-ref ar i) a) an)
           (if (= (vector-ref ar i) b) bn
             (&& (&& (= (vector-ref ar i) a) an) bn)) aux_1))))))

;;Wrapping for the sketch of the join.
(define (__join__ $L $R)
  (let ([an ($-an $L)] [bn ($-bn $L)] [aux_1 ($-aux_1 $L)] [x.an ($-an $R)]
    [x.bn ($-bn $R)] [x.aux_1 ($-aux_1 $R)])
    (let ([aux_1  (bExpr:boolean  an bn aux_1 x.an x.bn x.aux_1 1)])
       ($ (&& (bExpr:num->bool   an bn aux_1 x.an x.bn x.aux_1  1)
           (bExpr:boolean  an bn aux_1 x.an x.bn x.aux_1 1))
         (if (bExpr:num->bool   an bn aux_1 x.an x.bn x.aux_1  1)
           (bExpr:boolean  an bn aux_1 x.an x.bn x.aux_1 1)
           (&&
            (&& (bExpr:num->bool   an bn aux_1 x.an x.bn x.aux_1  1)
             (bExpr:boolean  an bn aux_1 x.an x.bn x.aux_1 1))
            (bExpr:boolean  an bn aux_1 x.an x.bn x.aux_1 1))) aux_1))))


;;Symbolic input state and synthesized id state
(define $_identity ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic aux_10 boolean?)
(define $_initial ($ #t #t (choose 0 1 #t #f)))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list tmp___0 tmp i b a    ar$1 ar$2 ar$3 ar$4 ar$5 ar$6 ar$7 ar$8 ar$9 ar$10)
  #:guarantee (assert (and
              ($-eq? (__loop_body__ $_initial 0 4)
                (__join__ (__loop_body__ $_initial 0 2) (__loop_body__ $_initial 2 4)))
              ($-eq? (__loop_body__ $_initial 0 9)
                (__join__ (__loop_body__ $_initial 0 3) (__loop_body__ $_initial 3 9)))
              ($-eq? (__loop_body__ $_initial 0 9)
                (__join__ (__loop_body__ $_initial 0 7) (__loop_body__ $_initial 7 9)))
              ($-eq? (__loop_body__ $_initial 2 9)
                (__join__ (__loop_body__ $_initial 2 7) (__loop_body__ $_initial 7 9)))))))

(print-forms odot)
