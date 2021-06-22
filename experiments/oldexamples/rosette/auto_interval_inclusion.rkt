#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(struct $iiiibii (low high l h incl aux_incl44 aux_incl45) #:transparent)
(define ($iiiibii-eq? s1 s2) (and (eq? ($iiiibii-low s1) ($iiiibii-low s2))
 (eq? ($iiiibii-high s1) ($iiiibii-high s2))
 (eq? ($iiiibii-l s1) ($iiiibii-l s2))  (eq? ($iiiibii-h s1) ($iiiibii-h s2))
 (eq? ($iiiibii-incl s1) ($iiiibii-incl s2))
 (eq? ($iiiibii-aux_incl44 s1) ($iiiibii-aux_incl44 s2))
 (eq? ($iiiibii-aux_incl45 s1) ($iiiibii-aux_incl45 s2))
))


(define-symbolic seq:high$0 seq:high$1 seq:high$2 seq:high$3 seq:high$4 seq:high$5 seq:high$6 seq:high$7 seq:high$8 integer?)
(define seq:high
  (list seq:high$0 seq:high$1 seq:high$2 seq:high$3 seq:high$4 seq:high$5 seq:high$6 seq:high$7 seq:high$8))
(define-symbolic seq:low$0 seq:low$1 seq:low$2 seq:low$3 seq:low$4 seq:low$5 seq:low$6 seq:low$7 seq:low$8 integer?)
(define seq:low
  (list seq:low$0 seq:low$1 seq:low$2 seq:low$3 seq:low$4 seq:low$5 seq:low$6 seq:low$7 seq:low$8))




;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  (Loop i_begin_ i_end_ 9 s
    (lambda (__s70 i)
      (let ([low ($iiiibii-low __s70)][high ($iiiibii-high __s70)]
        [l ($iiiibii-l __s70)][h ($iiiibii-h __s70)][incl ($iiiibii-incl __s70)]
        [aux_incl44 ($iiiibii-aux_incl44 __s70)]
        [aux_incl45 ($iiiibii-aux_incl45 __s70)])
        (let ([aux_incl44 (list-ref seq:high i_begin_)]
              [aux_incl45 (list-ref seq:low i_begin_)])
            (let ([low (min (list-ref seq:low i) (list-ref seq:high i))]
              [high (max (list-ref seq:high i) -1)])
               ($iiiibii
                 low
                 high
                 low
                 high
                 (if (! (<= high h)) #f (if (! (>= low l)) #f incl))
                 aux_incl44
                 aux_incl45)))))))

;;Wrapping for the sketch of the join.

;;-------------------------------
(define (__join__ left_state71 right_state72 i_start i_end)
  (let ([l.low ($iiiibii-low left_state71)]
    [l.high ($iiiibii-high left_state71)][l.l ($iiiibii-l left_state71)]
    [l.h ($iiiibii-h left_state71)][l.incl ($iiiibii-incl left_state71)]
    [l.aux_incl44 ($iiiibii-aux_incl44 left_state71)]
    [l.aux_incl45 ($iiiibii-aux_incl45 left_state71)])
     (let ([r.low ($iiiibii-low right_state72)]
       [r.high ($iiiibii-high right_state72)][r.l ($iiiibii-l right_state72)]
       [r.h ($iiiibii-h right_state72)][r.incl ($iiiibii-incl right_state72)]
       [r.aux_incl44 ($iiiibii-aux_incl44 right_state72)]
       [r.aux_incl45 ($iiiibii-aux_incl45 right_state72)])
       (let ([aux_incl44 l.aux_incl44]
             [aux_incl45 l.aux_incl45])
         (let ([low r.low]
               [high r.high])
           ($iiiibii
            low
            high
            r.low
            r.h
            (if
             ((ComparisonOps 0)
              (NumExprBasic
               l.aux_incl44
               r.aux_incl44
               l.h
               r.h
               l.aux_incl45
               r.aux_incl45
               l.l
               r.l
               l.high
               r.high
               l.low
               r.low
               0)
              (NumExprBasic
               l.aux_incl44
               r.aux_incl44
               l.h
               r.h
               l.aux_incl45
               r.aux_incl45
               l.l
               r.l
               l.high
               r.high
               l.low
               r.low
               0)) (BoolExpr r.incl 1)
             (if
              ((ComparisonOps 0)
               (NumExprBasic
                l.aux_incl44
                r.aux_incl44
                l.aux_incl45
                r.aux_incl45
                l.h
                r.h
                l.l
                r.l
                l.high
                r.high
                l.low
                r.low
                0)
               (NumExprBasic
                l.aux_incl44
                r.aux_incl44
                l.h
                r.h
                l.aux_incl45
                r.aux_incl45
                l.l
                r.l
                l.high
                r.high
                l.low
                r.low
                0))
              (BoolExpr r.incl 1)
              (BoolExpr l.incl r.incl 1)))

            aux_incl44
            aux_incl45))))))


;;Symbolic input state and synthesized id state
(define $_identity ($iiiibii
                    (choose 0 #t #f 10 -10 0)
                    (choose 0 #t #f 10 -10 0)
                    (choose 0 #t #f 10 -10 0)
                    (choose 0 #t #f 10 -10 0)
                    (choose 0 #t #f 10 -10 #t)
                    (choose 0 #t #f 10 -10)
                    (choose 0 #t #f 10 -10)))

(define ($_initial _begin_ end) ($iiiibii 0 0 0 0 #t
                                          (choose 0 #t #f 10 -10)
                                          (choose 0 #t #f 10 -10)))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list seq:high$0 seq:high$1 seq:high$2 seq:high$3 seq:high$4
             seq:low$0 seq:low$1 seq:low$2 seq:low$3 seq:low$4)
  #:guarantee (assert (and
              ($iiiibii-eq? (__loop_body__ ($_initial 0 2) 0 2 )
                (__join__ (__loop_body__ ($_initial 0 1) 0 1 ) (__loop_body__ ($_initial 1 2) 1 2 ) 0 2))
              ($iiiibii-eq? (__loop_body__ ($_initial 0 7) 0 7 )
                (__join__ (__loop_body__ ($_initial 0 1) 0 1 ) (__loop_body__ ($_initial 1 7) 1 7 ) 0 7))
              ($iiiibii-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 5) 2 5 ) 0 5))
              ($iiiibii-eq? (__loop_body__ ($_initial 0 8) 0 8 )
                (__join__ (__loop_body__ ($_initial 0 5) 0 5 ) (__loop_body__ ($_initial 5 8) 5 8 ) 0 8))
              ($iiiibii-eq? (__loop_body__ ($_initial 0 9) 0 9 )
                (__join__ (__loop_body__ ($_initial 0 3) 0 3 ) (__loop_body__ ($_initial 3 9) 3 9 ) 0 9))
              ($iiiibii-eq? (__loop_body__ ($_initial 0 3) 0 3 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 3) 2 3 ) 0 3))
              ($iiiibii-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                            (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 4) 2 4 ) 0 4))))))


(if (sat? odot) (print-forms odot) (print "UNSAT"))
