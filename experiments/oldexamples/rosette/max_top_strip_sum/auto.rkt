#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

;;Defining struct for state of the inner loop.
(struct $i (top_strip_sum) #:transparent)
(define ($i-eq? s1 s2)
  (and (eq? ($i-top_strip_sum s1) ($i-top_strip_sum s2))
       ))

(define-symbolic
  seq:top_strip_sum$0
  seq:top_strip_sum$1
  seq:top_strip_sum$2
  seq:top_strip_sum$3
  seq:top_strip_sum$4
  seq:top_strip_sum$5
  seq:top_strip_sum$6
  seq:top_strip_sum$7
  seq:top_strip_sum$8 integer?)

(define seq:top_strip_sum
  (list seq:top_strip_sum$0
        seq:top_strip_sum$1
        seq:top_strip_sum$2
        seq:top_strip_sum$3
        seq:top_strip_sum$4
        seq:top_strip_sum$5
        seq:top_strip_sum$6
        seq:top_strip_sum$7
        seq:top_strip_sum$8))

(struct $ii (top_strip_sum max_top_strip) #:transparent)

(define ($ii-eq? s1 s2)
  (and (eq? ($ii-top_strip_sum s1) ($ii-top_strip_sum s2))
       (eq? ($ii-max_top_strip s1) ($ii-max_top_strip s2))
       ))
;;Defining inner join function for outer loop.
(define (join#L__mto#6 $L $R j_start j_end)
  (let ([l.top_strip_sum ($i-top_strip_sum $L)]
        [r.top_strip_sum ($i-top_strip_sum $R)])
    ($i (+ l.top_strip_sum (+ r.top_strip_sum 0)))))


;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  (Loop i_begin_ i_end_ 9 s
        (lambda (__s1 i)
          (let ([top_strip_sum ($ii-top_strip_sum __s1)]
                [max_top_strip ($ii-max_top_strip __s1)])
            (let ([tup$ ($i (+ top_strip_sum
                               (+ (list-ref seq:top_strip_sum i) 0)))])
              (let ([top_strip_sum ($i-top_strip_sum tup$)])
                ($ii top_strip_sum (max max_top_strip top_strip_sum))))))))

;;Wrapping for the sketch of the join.
(define (__join__ left_state2 right_state3 i_start i_end)
  (let ([l.top_strip_sum ($ii-top_strip_sum left_state2)]
        [l.max_top_strip ($ii-max_top_strip left_state2)])
    (let ([r.top_strip_sum ($ii-top_strip_sum right_state3)]
          [r.max_top_strip ($ii-max_top_strip right_state3)])
      (let ([tup$ ($i (+
                       (NumExprArith
                        l.max_top_strip
                        r.max_top_strip
                        l.top_strip_sum
                        r.top_strip_sum
                        1)
                       (NumExprArith
                        r.max_top_strip
                        r.top_strip_sum
                        1)))])
        (let ([top_strip_sum ($i-top_strip_sum tup$)])
          ($ii top_strip_sum
               (max
                (NumExprBasic
                 l.max_top_strip
                 r.max_top_strip
                 l.top_strip_sum
                 r.top_strip_sum
                 1)
                (NumExprBasic
                 l.max_top_strip
                 r.max_top_strip
                 l.top_strip_sum
                 r.top_strip_sum
                 1))))))))


;;Symbolic input state and synthesized id state
(define $_identity ($ii (choose 0 #t #f 0) (choose 0 #t #f 0)))
(define ($_initial _begin_ end) ($ii 0 0))
;;Actual synthesis work happens here

(define odot
  (time
   (synthesize
    #:forall (list seq:top_strip_sum$0
                   seq:top_strip_sum$1
                   seq:top_strip_sum$2
                   seq:top_strip_sum$3
                   seq:top_strip_sum$4
                   seq:top_strip_sum$5
                   seq:top_strip_sum$6
                   seq:top_strip_sum$7
                   seq:top_strip_sum$8
                   )
    #:guarantee (assert (and
                         ($ii-eq? (__loop_body__ ($_initial 0 2) 0 2 )
                                  (__join__ (__loop_body__ ($_initial 0 1) 0 1 )
                                            (__loop_body__ ($_initial 1 2) 1 2 ) 0 2))
                         ($ii-eq? (__loop_body__ ($_initial 0 7) 0 7 )
                                  (__join__ (__loop_body__ ($_initial 0 1) 0 1 )
                                            (__loop_body__ ($_initial 1 7) 1 7 ) 0 7))
                         ($ii-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                                  (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                            (__loop_body__ ($_initial 2 5) 2 5 ) 0 5))
                         ($ii-eq? (__loop_body__ ($_initial 0 8) 0 8 )
                                  (__join__ (__loop_body__ ($_initial 0 5) 0 5 )
                                            (__loop_body__ ($_initial 5 8) 5 8 ) 0 8))
                         ($ii-eq? (__loop_body__ ($_initial 0 9) 0 9 )
                                  (__join__ (__loop_body__ ($_initial 0 3) 0 3 )
                                            (__loop_body__ ($_initial 3 9) 3 9 ) 0 9))
                         ($ii-eq? (__loop_body__ ($_initial 0 3) 0 3 )
                                  (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                            (__loop_body__ ($_initial 2 3) 2 3 ) 0 3))
                         ($ii-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                                  (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                            (__loop_body__ ($_initial 2 4) 2 4 ) 0 4)))))))

(if (sat? odot) (print-forms odot) (print 'UNSAT))


;; cpu time: 184 real time: 1250 gc time: 24

;; '(define (__join__ left_state2 right_state3 i_start i_end)
;;    (let ((l.top_strip_sum ($ii-top_strip_sum left_state2))
;;          (l.max_top_strip ($ii-max_top_strip left_state2)))
;;      (let ((r.top_strip_sum ($ii-top_strip_sum right_state3))
;;            (r.max_top_strip ($ii-max_top_strip right_state3)))
;;        (let ((tup$ ($i (+ (sub1 l.top_strip_sum) (add1 r.top_strip_sum)))))
;;          (let ((top_strip_sum ($i-top_strip_sum tup$)))
;;            ($ii
;;             top_strip_sum
;;             (max l.max_top_strip (+ r.max_top_strip l.top_strip_sum))))))))
