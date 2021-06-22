#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(struct $Vi_ (c) #:transparent)
(define ($Vi_-eq? s1 s2) (and (eq? ($Vi_-c s1) ($Vi_-c s2))
))


(define-symbolic mtr integer?)
(define-symbolic mtrl integer?)
(define-symbolic sum integer?)
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
(define-symbolic A18$0-c$0 A18$0-c$1 A18$0-c$2 A18$0-c$3 A18$0-c$4 integer?)
(define A18$0-c (list A18$0-c$0 A18$0-c$1 A18$0-c$2 A18$0-c$3 A18$0-c$4))
(define A18$0 ($Vi_ A18$0-c) )
(define-symbolic A18$1-c$0 A18$1-c$1 A18$1-c$2 A18$1-c$3 A18$1-c$4 integer?)
(define A18$1-c (list A18$1-c$0 A18$1-c$1 A18$1-c$2 A18$1-c$3 A18$1-c$4))
(define A18$1 ($Vi_ A18$1-c) )
(define-symbolic A18$2-c$0 A18$2-c$1 A18$2-c$2 A18$2-c$3 A18$2-c$4 integer?)
(define A18$2-c (list A18$2-c$0 A18$2-c$1 A18$2-c$2 A18$2-c$3 A18$2-c$4))
(define A18$2 ($Vi_ A18$2-c) )
(define-symbolic A18$3-c$0 A18$3-c$1 A18$3-c$2 A18$3-c$3 A18$3-c$4 integer?)
(define A18$3-c (list A18$3-c$0 A18$3-c$1 A18$3-c$2 A18$3-c$3 A18$3-c$4))
(define A18$3 ($Vi_ A18$3-c) )
(define-symbolic A18$4-c$0 A18$4-c$1 A18$4-c$2 A18$4-c$3 A18$4-c$4 integer?)
(define A18$4-c (list A18$4-c$0 A18$4-c$1 A18$4-c$2 A18$4-c$3 A18$4-c$4))
(define A18$4 ($Vi_ A18$4-c) )
(define-symbolic A18$5-c$0 A18$5-c$1 A18$5-c$2 A18$5-c$3 A18$5-c$4 integer?)
(define A18$5-c (list A18$5-c$0 A18$5-c$1 A18$5-c$2 A18$5-c$3 A18$5-c$4))
(define A18$5 ($Vi_ A18$5-c) )
(define-symbolic A18$6-c$0 A18$6-c$1 A18$6-c$2 A18$6-c$3 A18$6-c$4 integer?)
(define A18$6-c (list A18$6-c$0 A18$6-c$1 A18$6-c$2 A18$6-c$3 A18$6-c$4))
(define A18$6 ($Vi_ A18$6-c) )
(define-symbolic A18$7-c$0 A18$7-c$1 A18$7-c$2 A18$7-c$3 A18$7-c$4 integer?)
(define A18$7-c (list A18$7-c$0 A18$7-c$1 A18$7-c$2 A18$7-c$3 A18$7-c$4))
(define A18$7 ($Vi_ A18$7-c) )
(define-symbolic A18$8-c$0 A18$8-c$1 A18$8-c$2 A18$8-c$3 A18$8-c$4 integer?)
(define A18$8-c (list A18$8-c$0 A18$8-c$1 A18$8-c$2 A18$8-c$3 A18$8-c$4))
(define A18$8 ($Vi_ A18$8-c) )
(define A18 (list A18$0 A18$1 A18$2 A18$3 A18$4 A18$5 A18$6 A18$7 A18$8))




;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  (Loop i_begin_ i_end_ 9 s
    (lambda (__s28 i)
      (let ([c ($Vi_-c __s28)])
         (let ([x_ (LoopFunc 0 (lambda (j) (> 5 j)) (lambda (j) (add1 j))
                     ($Vi_
                       c)
                     (lambda (s17 j) (let ([c ($Vi_-c s17)])
                                        (let ([c (list-set
                                                   c
                                                   j
                                                   (+
                                                    (list-ref (list-ref seq:c i) j)
                                                    (list-ref c j)))])
                                           ($Vi_
                                             c)))))])
            (let ([c ($Vi_-c x_)])  ($Vi_
                                      c)))))))

;;Wrapping for the sketch of the join.

;;-------------------------------
(define (__join__ left_state29 right_state30 i_start i_end)
  (let ([l.c ($Vi_-c left_state29)])
     (let ([r.c ($Vi_-c right_state30)])
        (let ([x_ (LoopFunc 0 (lambda (j) (< j 5)) (lambda (j) (add1 j))
                    ($Vi_
                      l.c)
                    (lambda (s17 j) (let ([c ($Vi_-c s17)])
                                       (let ([c (list-set
                                                  c
                                                  j
                                                  (+
                                                   (NumExprBasic
                                                     (list-ref r.c j)
                                                     1)
                                                   (NumExprBasic
                                                     (list-ref l.c j)
                                                     (list-ref r.c j)
                                                     1)))])  ($Vi_
                                                               c)))))])
           (let ([c ($Vi_-c x_)])  ($Vi_
                                     c))))))


;;Symbolic input state and synthesized id state
(define $_identity ($Vi_ (make-list 5 (choose 0 #t #f))))
(define ($_initial _begin_ end) ($Vi_ (make-list 5 (choose 0 #t #f))))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list j_start j_end sum mtrl mtr seq:sum$0 seq:sum$1 seq:sum$2
             seq:sum$3 seq:sum$4 seq:c$0$0 seq:c$0$1 seq:c$0$2 seq:c$0$3
             seq:c$0$4 seq:c$1$0 seq:c$1$1 seq:c$1$2 seq:c$1$3 seq:c$1$4
             seq:c$2$0 seq:c$2$1 seq:c$2$2 seq:c$2$3 seq:c$2$4 seq:c$3$0
             seq:c$3$1 seq:c$3$2 seq:c$3$3 seq:c$3$4 seq:c$4$0 seq:c$4$1
             seq:c$4$2 seq:c$4$3 seq:c$4$4 seq:c$5$0 seq:c$5$1 seq:c$5$2
             seq:c$5$3 seq:c$5$4 seq:c$6$0 seq:c$6$1 seq:c$6$2 seq:c$6$3
             seq:c$6$4 seq:c$7$0 seq:c$7$1 seq:c$7$2 seq:c$7$3 seq:c$7$4
             seq:c$8$0 seq:c$8$1 seq:c$8$2 seq:c$8$3 seq:c$8$4 A18$0-c$0
             A18$0-c$1 A18$0-c$2 A18$0-c$3 A18$0-c$4 A18$1-c$0 A18$1-c$1
             A18$1-c$2 A18$1-c$3 A18$1-c$4 A18$2-c$0 A18$2-c$1 A18$2-c$2
             A18$2-c$3 A18$2-c$4 A18$3-c$0 A18$3-c$1 A18$3-c$2 A18$3-c$3
             A18$3-c$4 A18$4-c$0 A18$4-c$1 A18$4-c$2 A18$4-c$3 A18$4-c$4
             A18$5-c$0 A18$5-c$1 A18$5-c$2 A18$5-c$3 A18$5-c$4 A18$6-c$0
             A18$6-c$1 A18$6-c$2 A18$6-c$3 A18$6-c$4 A18$7-c$0 A18$7-c$1
             A18$7-c$2 A18$7-c$3 A18$7-c$4 A18$8-c$0 A18$8-c$1 A18$8-c$2
             A18$8-c$3 A18$8-c$4)
  #:guarantee (assert (and
              ($Vi_-eq? (__loop_body__ ($_initial 0 2) 0 2 )
                (__join__ (__loop_body__ ($_initial 0 1) 0 1 ) (__loop_body__ ($_initial 1 2) 1 2 ) 0 2))
              ($Vi_-eq? (__loop_body__ ($_initial 0 7) 0 7 )
                (__join__ (__loop_body__ ($_initial 0 1) 0 1 ) (__loop_body__ ($_initial 1 7) 1 7 ) 0 7))
              ($Vi_-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 5) 2 5 ) 0 5))
              ($Vi_-eq? (__loop_body__ ($_initial 0 8) 0 8 )
                (__join__ (__loop_body__ ($_initial 0 5) 0 5 ) (__loop_body__ ($_initial 5 8) 5 8 ) 0 8))
              ($Vi_-eq? (__loop_body__ ($_initial 0 9) 0 9 )
                (__join__ (__loop_body__ ($_initial 0 3) 0 3 ) (__loop_body__ ($_initial 3 9) 3 9 ) 0 9))
              ($Vi_-eq? (__loop_body__ ($_initial 0 3) 0 3 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 3) 2 3 ) 0 3))
              ($Vi_-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 4) 2 4 ) 0 4))))))
