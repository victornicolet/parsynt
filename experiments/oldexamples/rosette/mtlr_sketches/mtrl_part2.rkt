#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(struct $Vi_ii (c mtr sum) #:transparent)
(define ($Vi_ii-eq? s1 s2) (and (eq? ($Vi_ii-c s1) ($Vi_ii-c s2))
 (eq? ($Vi_ii-mtr s1) ($Vi_ii-mtr s2))  (eq? ($Vi_ii-sum s1) ($Vi_ii-sum s2))
))


(define-symbolic mtrl integer?)
(define-symbolic j_end integer?)
(define-symbolic j_start integer?)
(define-symbolic seq:sum$0 seq:sum$1 seq:sum$2 seq:sum$3 seq:sum$4 seq:sum$5 seq:sum$6 seq:sum$7 seq:sum$8 integer?)
(define seq:sum
  (list seq:sum$0 seq:sum$1 seq:sum$2 seq:sum$3 seq:sum$4 seq:sum$5 seq:sum$6 seq:sum$7 seq:sum$8))
(define-symbolic seq:c$0$0 seq:c$0$1 seq:c$0$2 seq:c$0$3 seq:c$0$4 integer?)
(define seq:c$0 (list seq:c$0$0 seq:c$0$1 seq:c$0$2 seq:c$0$3 seq:c$0$4))
(define-symbolic seq:c$1$0 seq:c$1$1 seq:c$1$2 seq:c$1$3 seq:c$1$4 integer?)
(define seq:c$1 (list seq:c$1$0 seq:c$1$1 seq:c$1$2 seq:c$1$3 seq:c$1$4))
(define-symbolic seq:c$2$0 seq:c$2$1 seq:c$2$2 seq:c$2$3 seq:c$2$4 integer?)
(define seq:c$2 (list seq:c$2$0 seq:c$2$1 seq:c$2$2 seq:c$2$3 seq:c$2$4))
(define-symbolic seq:c$3$0 seq:c$3$1 seq:c$3$2 seq:c$3$3 seq:c$3$4 integer?)
(define seq:c$3 (list seq:c$3$0 seq:c$3$1 seq:c$3$2 seq:c$3$3 seq:c$3$4))
(define-symbolic seq:c$4$0 seq:c$4$1 seq:c$4$2 seq:c$4$3 seq:c$4$4 integer?)
(define seq:c$4 (list seq:c$4$0 seq:c$4$1 seq:c$4$2 seq:c$4$3 seq:c$4$4))
(define-symbolic seq:c$5$0 seq:c$5$1 seq:c$5$2 seq:c$5$3 seq:c$5$4 integer?)
(define seq:c$5 (list seq:c$5$0 seq:c$5$1 seq:c$5$2 seq:c$5$3 seq:c$5$4))
(define-symbolic seq:c$6$0 seq:c$6$1 seq:c$6$2 seq:c$6$3 seq:c$6$4 integer?)
(define seq:c$6 (list seq:c$6$0 seq:c$6$1 seq:c$6$2 seq:c$6$3 seq:c$6$4))
(define-symbolic seq:c$7$0 seq:c$7$1 seq:c$7$2 seq:c$7$3 seq:c$7$4 integer?)
(define seq:c$7 (list seq:c$7$0 seq:c$7$1 seq:c$7$2 seq:c$7$3 seq:c$7$4))
(define-symbolic seq:c$8$0 seq:c$8$1 seq:c$8$2 seq:c$8$3 seq:c$8$4 integer?)
(define seq:c$8 (list seq:c$8$0 seq:c$8$1 seq:c$8$2 seq:c$8$3 seq:c$8$4))
(define seq:c
  (list seq:c$0 seq:c$1 seq:c$2 seq:c$3 seq:c$4 seq:c$5 seq:c$6 seq:c$7 seq:c$8))


;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  (Loop i_begin_ i_end_ 9 s
    (lambda (__s34 i)
      (let ([c ($Vi_ii-c __s34)]
            [mtr ($Vi_ii-mtr __s34)]
            [sum ($Vi_ii-sum __s34)])
        (let ([x_22
               (LoopFunc
                0
                (lambda (j) (> 5 j))
                (lambda (j) (add1 j))
                ($Vi_ii c 0 0)
                (lambda (s23 j) (let ([c ($Vi_ii-c s23)]
                                      [mtr ($Vi_ii-mtr s23)]
                                      [sum ($Vi_ii-sum s23)])
                                  (let ([c (list-set
                                            c
                                            j
                                            (+
                                             (list-ref (list-ref seq:c i) j)
                                             (list-ref c j)))])
                                    ($Vi_ii
                                     c
                                     (max mtr (list-ref c j))
                                     sum)))))])
          (let ([c ($Vi_ii-c x_22)]
                [mtr ($Vi_ii-mtr x_22)]
                [sum (list-ref seq:sum i)])
            ($Vi_ii c mtr sum)))))))

;;Wrapping for the sketch of the join.

;;-------------------------------
(define (__join__ left_state35 right_state36 i_start i_end)
  (let ([l.c ($Vi_ii-c left_state35)][l.mtr ($Vi_ii-mtr left_state35)]
    [l.sum ($Vi_ii-sum left_state35)])
     (let ([r.c ($Vi_ii-c right_state36)][r.mtr ($Vi_ii-mtr right_state36)]
       [r.sum ($Vi_ii-sum right_state36)])
       (let ([x_22 (LoopFunc
                    0
                    (lambda (j) (< j 5))
                    (lambda (j) (add1 j))
                    ($Vi_ii
                     l.c
                     0
                     0)
                    (lambda (s23 j)
                      (let ([c ($Vi_ii-c s23)]
                            [mtr ($Vi_ii-mtr s23)]
                            [sum ($Vi_ii-sum s23)])
                        (let ([c (list-set
                                  c
                                  j
                                  (+ (list-ref r.c j)
                                     (list-ref l.c j)))])
                          ($Vi_ii
                           c
                           (max

                            (NumExprBasic
                             sum
                             r.sum
                             l.sum
                             mtr
                             r.mtr
                             l.mtr
                             (list-ref c j)
                             (list-ref r.c j)
                             (list-ref l.c j)
                             0)

                            (NumExprBasic
                             sum
                             r.sum
                             l.sum
                             mtr
                             r.mtr
                             l.mtr
                             (list-ref c j)
                             (list-ref r.c j)
                             (list-ref l.c j)
                             0)
                            )
                           sum)))))])
         (let ([c ($Vi_ii-c x_22)][mtr ($Vi_ii-mtr x_22)][sum r.sum])
           ($Vi_ii
            c
            mtr
            sum))))))


;;Symbolic input state and synthesized id state
(define $_identity ($Vi_ii (make-list 5 (choose 0 #t #f)) (choose 0 #t #f 0) (choose 0 #t #f 0)))
(define ($_initial _begin_ end) ($Vi_ii (make-list 5 0) 0 0))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list j_start j_end mtrl seq:sum$0 seq:sum$1 seq:sum$2 seq:sum$3
             seq:sum$4 seq:c$0$0 seq:c$0$1 seq:c$0$2 seq:c$0$3 seq:c$0$4
             seq:c$1$0 seq:c$1$1 seq:c$1$2 seq:c$1$3 seq:c$1$4 seq:c$2$0
             seq:c$2$1 seq:c$2$2 seq:c$2$3 seq:c$2$4 seq:c$3$0 seq:c$3$1
             seq:c$3$2 seq:c$3$3 seq:c$3$4 seq:c$4$0 seq:c$4$1 seq:c$4$2
             seq:c$4$3 seq:c$4$4 seq:c$5$0 seq:c$5$1 seq:c$5$2 seq:c$5$3
             seq:c$5$4 seq:c$6$0 seq:c$6$1 seq:c$6$2 seq:c$6$3 seq:c$6$4
             seq:c$7$0 seq:c$7$1 seq:c$7$2 seq:c$7$3 seq:c$7$4 seq:c$8$0
             seq:c$8$1 seq:c$8$2 seq:c$8$3 seq:c$8$4)
  #:guarantee (assert (and
              ($Vi_ii-eq? (__loop_body__ ($_initial 0 2) 0 2 )
                (__join__ (__loop_body__ ($_initial 0 1) 0 1 ) (__loop_body__ ($_initial 1 2) 1 2 ) 0 2))
              ($Vi_ii-eq? (__loop_body__ ($_initial 0 7) 0 7 )
                (__join__ (__loop_body__ ($_initial 0 1) 0 1 ) (__loop_body__ ($_initial 1 7) 1 7 ) 0 7))
              ($Vi_ii-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 5) 2 5 ) 0 5))
              ($Vi_ii-eq? (__loop_body__ ($_initial 0 8) 0 8 )
                (__join__ (__loop_body__ ($_initial 0 5) 0 5 ) (__loop_body__ ($_initial 5 8) 5 8 ) 0 8))
              ($Vi_ii-eq? (__loop_body__ ($_initial 0 9) 0 9 )
                (__join__ (__loop_body__ ($_initial 0 3) 0 3 ) (__loop_body__ ($_initial 3 9) 3 9 ) 0 9))
              ($Vi_ii-eq? (__loop_body__ ($_initial 0 3) 0 3 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 3) 2 3 ) 0 3))
              ($Vi_ii-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 4) 2 4 ) 0 4))))))

(if (sat? odot) (print-forms odot) (print "UNSAT"))
