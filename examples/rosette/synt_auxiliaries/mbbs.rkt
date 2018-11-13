#lang rosette
;; This is an experiment designed to show that using synthesis to synthesize the auxliary, at the same time as synthesizing the join, has a huge performance penalty. Even using the simplest sketch mutliplies the synthesis time by 30.
;; Using a natural sketch for the auxiliary ('any arithmetic expression of depth 1') already results in perforamce at least 100 times slower.
;; While we are not concerned in making our algorithms work for compilers, and output a result in a few miliseconds, this shows that our choice of deductive synthesis with auxiliaries is much better. To make direct syntax guided synthesis work for this problem, one would need to invest the same amount of work (as the auxiliary discovery) to restrict the sketch to a tractable problem.

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

;;Defining struct for state of the inner loop.
(struct $i (plane_sum) #:transparent)
(define ($i-eq? s1 s2) (and (eq? ($i-plane_sum s1) ($i-plane_sum s2))))

(define-symbolic in_lp0 in_lp1 in_lp2 in_lp3 in_lp4 in_lp5 in_lp6 in_lp7 in_lp8 integer?)

(define inner_loop (list in_lp0 in_lp1 in_lp2 in_lp3 in_lp4 in_lp5 in_lp6 in_lp7 in_lp8))

(struct $iii (plane_sum max_top_strip aux) #:transparent)

(define ($iii-eq? s1 s2)
  (and (eq? ($iii-plane_sum s1) ($iii-plane_sum s2))
       (eq? ($iii-max_top_strip s1) ($iii-max_top_strip s2))
       (eq? ($iii-aux s1) ($iii-aux s2))
       ))

;;Defining inner join function for outer loop.
(define (join#L__mto#6 $L $R j_start j_end)
  (let ([l.plane_sum ($i-plane_sum $L)]
        [r.plane_sum ($i-plane_sum $R)])
    ($i r.plane_sum)))


;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  (Loop i_begin_ i_end_ 9 s
        (lambda (__s1 i)
          (let ([plane_sum ($iii-plane_sum __s1)]
                [max_top_strip ($iii-max_top_strip __s1)]
                [aux ($iii-aux __s1)])
            (let ([plane_sum (list-ref inner_loop i)])
              ($iii plane_sum
                   (max (+ max_top_strip plane_sum) 0)
                   ;; ((choose + - max min) aux (choose max_top_strip plane_sum)) Contrained version: 27.7 s
                   (NumExprBasic aux max_top_strip plane_sum 1)
                   ))))))

;;Wrapping for the sketch of the join.
(define (__join__ left_state2 right_state3 i_start i_end)
  (let ([l.plane_sum ($iii-plane_sum left_state2)]
        [l.max_top_strip ($iii-max_top_strip left_state2)]
        [r.plane_sum ($iii-plane_sum right_state3)]
        [r.max_top_strip ($iii-max_top_strip right_state3)]
        [r.aux ($iii-aux right_state3)]
        [l.aux ($iii-aux left_state2)])
          ($iii r.plane_sum
               (max
                (NumExprBasic
                 l.max_top_strip
                 r.max_top_strip
                 l.plane_sum
                 r.plane_sum
                 l.aux
                 r.aux
                 1)
                (NumExprBasic
                 l.max_top_strip
                 r.max_top_strip
                 l.plane_sum
                 r.plane_sum
                 l.aux
                 r.aux
                 1))                    ; join part for max_top_strip
               (NumExprBasic
                l.max_top_strip
                 r.max_top_strip
                 l.plane_sum
                 r.plane_sum
                 l.aux
                 r.aux
                 1)                     ; join part for aux
                )))


;;Symbolic input state and synthesized id state
(define $_identity ($iii (choose 0 #t #f 0) (choose 0 #t #f 0) (choose 0 #t #f 0)))
(define ($_initial _begin_ end) ($iii 0 0 0))
;;Actual synthesis work happens here

(define odot
  (time
   (synthesize
    #:forall (list in_lp0 in_lp1 in_lp2 in_lp3 in_lp4
                   in_lp5 in_lp6 in_lp7 in_lp8)
    #:guarantee (assert (and
                         ($iii-eq? (__loop_body__ ($_initial 0 2) 0 2 )
                                  (__join__ (__loop_body__ ($_initial 0 1) 0 1 )
                                            (__loop_body__ ($_initial 1 2) 1 2 ) 0 2))
                         ($iii-eq? (__loop_body__ ($_initial 0 7) 0 7 )
                                  (__join__ (__loop_body__ ($_initial 0 1) 0 1 )
                                            (__loop_body__ ($_initial 1 7) 1 7 ) 0 7))
                         ($iii-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                                  (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                            (__loop_body__ ($_initial 2 5) 2 5 ) 0 5))
                         ($iii-eq? (__loop_body__ ($_initial 0 8) 0 8 )
                                  (__join__ (__loop_body__ ($_initial 0 5) 0 5 )
                                            (__loop_body__ ($_initial 5 8) 5 8 ) 0 8))
                         ($iii-eq? (__loop_body__ ($_initial 0 9) 0 9 )
                                  (__join__ (__loop_body__ ($_initial 0 3) 0 3 )
                                            (__loop_body__ ($_initial 3 9) 3 9 ) 0 9))
                         ($iii-eq? (__loop_body__ ($_initial 0 3) 0 3 )
                                  (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                            (__loop_body__ ($_initial 2 3) 2 3 ) 0 3))
                         ($iii-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                                  (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                            (__loop_body__ ($_initial 2 4) 2 4 ) 0 4)))))))

(if (sat? odot) (print-forms odot) (print 'UNSAT))

;; cpu time: 560 real time: 2536901 gc time: 60
;; /home/victorn/repos/parsynt/examples/rosette/synt_auxiliaries/mbbs.rkt:35:0
;; '(define (__loop_body__ s i_begin_ i_end_)
;;    (Loop
;;     i_begin_
;;     i_end_
;;     9
;;     s
;;     (lambda (__s1 i)
;;       (let ((plane_sum ($iii-plane_sum __s1))
;;             (max_top_strip ($iii-max_top_strip __s1))
;;             (aux ($iii-aux __s1)))
;;         (let ((plane_sum (list-ref inner_loop i)))
;;           ($iii
;;            plane_sum
;;            (max (+ max_top_strip plane_sum) 0)
;;            (- aux plane_sum)))))))
;; /home/victorn/repos/parsynt/examples/rosette/synt_auxiliaries/mbbs.rkt:49:0
;; '(define (__join__ left_state2 right_state3 i_start i_end)
;;    (let ((l.plane_sum ($iii-plane_sum left_state2))
;;          (l.max_top_strip ($iii-max_top_strip left_state2))
;;          (r.plane_sum ($iii-plane_sum right_state3))
;;          (r.max_top_strip ($iii-max_top_strip right_state3))
;;          (r.aux ($iii-aux right_state3))
;;          (l.aux ($iii-aux left_state2)))
;;      ($iii
;;       r.plane_sum
;;       (max (- l.max_top_strip r.aux) (max -1 r.max_top_strip))
;;       (+ r.aux l.aux))))
;; racket mbbs.rkt  2.06s user 0.22s system 0% cpu 42:18.56 total
