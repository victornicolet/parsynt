#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

;;Defining struct for state of the inner loop.
(struct $i (top_strip_sum) #:transparent)
(define ($i-eq? s1 s2)
  (and (eq? ($i-top_strip_sum s1) ($i-top_strip_sum s2))
       ))


(define-symbolic a$0$0 a$0$1 a$0$2 a$0$3 a$0$4 integer?)
(define a$0 (list a$0$0 a$0$1 a$0$2 a$0$3 a$0$4))
(define-symbolic a$1$0 a$1$1 a$1$2 a$1$3 a$1$4 integer?)
(define a$1 (list a$1$0 a$1$1 a$1$2 a$1$3 a$1$4))
(define-symbolic a$2$0 a$2$1 a$2$2 a$2$3 a$2$4 integer?)
(define a$2 (list a$2$0 a$2$1 a$2$2 a$2$3 a$2$4))
(define-symbolic a$3$0 a$3$1 a$3$2 a$3$3 a$3$4 integer?)
(define a$3 (list a$3$0 a$3$1 a$3$2 a$3$3 a$3$4))
(define-symbolic a$4$0 a$4$1 a$4$2 a$4$3 a$4$4 integer?)
(define a$4 (list a$4$0 a$4$1 a$4$2 a$4$3 a$4$4))
(define-symbolic a$5$0 a$5$1 a$5$2 a$5$3 a$5$4 integer?)
(define a$5 (list a$5$0 a$5$1 a$5$2 a$5$3 a$5$4))
(define-symbolic a$6$0 a$6$1 a$6$2 a$6$3 a$6$4 integer?)
(define a$6 (list a$6$0 a$6$1 a$6$2 a$6$3 a$6$4))
(define-symbolic a$7$0 a$7$1 a$7$2 a$7$3 a$7$4 integer?)
(define a$7 (list a$7$0 a$7$1 a$7$2 a$7$3 a$7$4))
(define-symbolic a$8$0 a$8$1 a$8$2 a$8$3 a$8$4 integer?)
(define a$8 (list a$8$0 a$8$1 a$8$2 a$8$3 a$8$4))

(define a (list
           a$0
           a$1
           a$2
           a$3
           a$4
           a$5
           a$6
           a$7
           a$8))



(struct $iiii (top_strip_sum
               max_top_strip
               max_seg_strip
               max_bot_strip) #:transparent)

(define ($iiii-eq? s1 s2)
  (and (eq? ($iiii-top_strip_sum s1) ($iiii-top_strip_sum s2))
       (eq? ($iiii-max_top_strip s1) ($iiii-max_top_strip s2))
       (eq? ($iiii-max_bot_strip s1) ($iiii-max_bot_strip s2))
       (eq? ($iiii-max_seg_strip s1) ($iiii-max_seg_strip s2))))

;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  (Loop i_begin_ i_end_ 9 s
        (lambda (__s1 i)
          (let ([top_strip_sum ($iiii-top_strip_sum __s1)]
                [max_top_strip ($iiii-max_top_strip __s1)]
                [max_seg_strip ($iiii-max_seg_strip __s1)]
                [max_bot_strip ($iiii-max_bot_strip __s1)])

            (let ([tup$
                   (LoopFunc
                    0
                    (lambda (j) (< j 5))
                    (lambda (j) (add1 j))
                    ($i 0)
                    (lambda (__s j)
                      (let ([top_strip_sum ($i-top_strip_sum __s)])
                        ($i (+ top_strip_sum (list-ref (list-ref a i) j))))))])


              (let ([top_strip_sum (+ top_strip_sum ($i-top_strip_sum tup$))])

                (let ([max_bot_strip
                       (max (+ max_bot_strip
                               ($i-top_strip_sum tup$)) 0)])

                  ($iiii top_strip_sum
                         (max max_top_strip top_strip_sum)
                         (max max_seg_strip max_bot_strip)
                         max_bot_strip))))))))


;;Wrapping for the sketch of the join.
(define (__join__ left_state2 right_state3 i_start i_end)
  (let ([l.top_strip_sum ($iiii-top_strip_sum left_state2)]
        [l.max_top_strip ($iiii-max_top_strip left_state2)]
        [l.max_seg_strip ($iiii-max_seg_strip left_state2)]
        [l.max_bot_strip ($iiii-max_bot_strip left_state2)])
    (let ([r.top_strip_sum ($iiii-top_strip_sum right_state3)]
          [r.max_top_strip ($iiii-max_top_strip right_state3)]
          [r.max_seg_strip ($iiii-max_seg_strip right_state3)]
          [r.max_bot_strip ($iiii-max_bot_strip right_state3)])
      (let ([tup$ ($i (+
                       (NumExprArith
                        l.max_top_strip
                        l.max_bot_strip
                        l.max_seg_strip
                        r.max_bot_strip
                        r.max_seg_strip
                        r.max_top_strip
                        l.top_strip_sum
                        r.top_strip_sum
                        1)
                       (NumExprArith
                        l.max_top_strip
                        l.max_bot_strip
                        l.max_seg_strip
                        r.max_bot_strip
                        r.max_seg_strip
                        r.max_top_strip
                        l.top_strip_sum
                        r.top_strip_sum
                        1)))])
        (let ([top_strip_sum ($i-top_strip_sum tup$)])
          (let ([max_bot_strip
                 (max
                  (NumExprBasic
                   l.max_bot_strip
                   l.max_seg_strip
                   r.max_bot_strip
                   r.max_seg_strip
                   l.max_top_strip
                   r.max_top_strip
                   l.top_strip_sum
                   r.top_strip_sum
                   1)
                  (NumExprArith
                   l.max_bot_strip
                   l.max_seg_strip
                   r.max_bot_strip
                   r.max_seg_strip
                   l.max_top_strip
                   r.max_top_strip
                   l.top_strip_sum
                   r.top_strip_sum
                   1))])
            ($iiii top_strip_sum
                   (max
                    (NumExprBasic
                     l.max_bot_strip
                     l.max_seg_strip
                     r.max_bot_strip
                     r.max_seg_strip
                     l.max_top_strip
                     r.max_top_strip
                     l.top_strip_sum
                     r.top_strip_sum
                     1)
                    (NumExprBasic
                     l.max_bot_strip
                     l.max_seg_strip
                     r.max_bot_strip
                     r.max_seg_strip
                     l.max_top_strip
                     r.max_top_strip
                     l.top_strip_sum
                     r.top_strip_sum
                     1))
                   (max
                    (NumExprBasic
                     l.max_bot_strip
                     l.max_seg_strip
                     r.max_bot_strip
                     r.max_seg_strip
                     l.max_top_strip
                     r.max_top_strip
                     l.top_strip_sum
                     r.top_strip_sum
                     2)
                    (NumExprBasic
                     l.max_bot_strip
                     l.max_seg_strip
                     r.max_bot_strip
                     r.max_seg_strip
                     l.max_top_strip
                     r.max_top_strip
                     l.top_strip_sum
                     r.top_strip_sum
                     2))
                   max_bot_strip)))))))


;;Symbolic input state and synthesized id state

(define ($_initial _begin_ end) ($iiii 0 0 0 0))
;;Actual synthesis work happens here

(define odot
  (time
   (synthesize
    #:forall (list
              a$0$0 a$0$1 a$0$2 a$0$3 a$0$4
              a$1$0 a$1$1 a$1$2 a$1$3 a$1$4
              a$2$0 a$2$1 a$2$2 a$2$3 a$2$4
              a$3$0 a$3$1 a$3$2 a$3$3 a$3$4
              a$4$0 a$4$1 a$4$2 a$4$3 a$4$4
              a$5$0 a$5$1 a$5$2 a$5$3 a$5$4
              a$6$0 a$6$1 a$6$2 a$6$3 a$6$4
              a$7$0 a$7$1 a$7$2 a$7$3 a$7$4
              a$8$0 a$8$1 a$8$2 a$8$3 a$8$4
              )
    #:guarantee (assert (and
                         ($iiii-eq? (__loop_body__ ($_initial 0 2) 0 2 )
                                    (__join__ (__loop_body__ ($_initial 0 1) 0 1 )
                                              (__loop_body__ ($_initial 1 2) 1 2 ) 0 2))
                         ($iiii-eq? (__loop_body__ ($_initial 0 7) 0 7 )
                                    (__join__ (__loop_body__ ($_initial 0 1) 0 1 )
                                              (__loop_body__ ($_initial 1 7) 1 7 ) 0 7))
                         ($iiii-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                                    (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                              (__loop_body__ ($_initial 2 5) 2 5 ) 0 5))
                         ($iiii-eq? (__loop_body__ ($_initial 0 8) 0 8 )
                                    (__join__ (__loop_body__ ($_initial 0 5) 0 5 )
                                              (__loop_body__ ($_initial 5 8) 5 8 ) 0 8))
                         ($iiii-eq? (__loop_body__ ($_initial 0 9) 0 9 )
                                    (__join__ (__loop_body__ ($_initial 0 3) 0 3 )
                                              (__loop_body__ ($_initial 3 9) 3 9 ) 0 9))
                         ($iiii-eq? (__loop_body__ ($_initial 0 3) 0 3 )
                                    (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                              (__loop_body__ ($_initial 2 3) 2 3 ) 0 3))
                         ($iiii-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                                    (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                              (__loop_body__ ($_initial 2 4) 2 4 ) 0 4)))))))

(if (sat? odot) (print-forms odot) (print 'UNSAT))


;; cpu time: 1312 real time: 147996 gc time: 76

;; '(define (__join__ left_state2 right_state3 i_start i_end)
;;    (let ((l.top_strip_sum ($iiii-top_strip_sum left_state2))
;;          (l.max_top_strip ($iiii-max_top_strip left_state2))
;;          (l.max_seg_strip ($iiii-max_seg_strip left_state2))
;;          (l.max_bot_strip ($iiii-max_bot_strip left_state2)))
;;      (let ((r.top_strip_sum ($iiii-top_strip_sum right_state3))
;;            (r.max_top_strip ($iiii-max_top_strip right_state3))
;;            (r.max_seg_strip ($iiii-max_seg_strip right_state3))
;;            (r.max_bot_strip ($iiii-max_bot_strip right_state3)))
;;        (let ((tup$
;;               ($i
;;                (+
;;                 (- l.top_strip_sum l.max_seg_strip)
;;                 (+ r.top_strip_sum l.max_seg_strip)))))
;;          (let ((top_strip_sum ($i-top_strip_sum tup$)))
;;            (let ((max_bot_strip
;;                   (max (+ l.max_bot_strip r.top_strip_sum) r.max_bot_strip)))
;;              ($iiii
;;               top_strip_sum
;;               (max l.max_top_strip (+ l.top_strip_sum r.max_top_strip))
;;               (max
;;                (max
;;                 (max l.max_seg_strip r.max_seg_strip)
;;                 (sub1 r.max_seg_strip))
;;                (+ (+ 4 r.max_top_strip) (- l.max_bot_strip 4)))
;;               max_bot_strip)))))))
