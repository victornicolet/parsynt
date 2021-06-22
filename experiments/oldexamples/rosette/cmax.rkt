#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(struct $Vi_i (mins cmax) #:transparent)
(define ($Vi_i-eq? s1 s2) (and (eq? ($Vi_i-mins s1) ($Vi_i-mins s2))
 (eq? ($Vi_i-cmax s1) ($Vi_i-cmax s2))
))



(define-symbolic A$0$0 A$0$1 A$0$2 A$0$3 A$0$4 integer?)
(define A$0 (list A$0$0 A$0$1 A$0$2 A$0$3 A$0$4))
(define-symbolic A$1$0 A$1$1 A$1$2 A$1$3 A$1$4 integer?)
(define A$1 (list A$1$0 A$1$1 A$1$2 A$1$3 A$1$4))
(define-symbolic A$2$0 A$2$1 A$2$2 A$2$3 A$2$4 integer?)
(define A$2 (list A$2$0 A$2$1 A$2$2 A$2$3 A$2$4))
(define-symbolic A$3$0 A$3$1 A$3$2 A$3$3 A$3$4 integer?)
(define A$3 (list A$3$0 A$3$1 A$3$2 A$3$3 A$3$4))
(define-symbolic A$4$0 A$4$1 A$4$2 A$4$3 A$4$4 integer?)
(define A$4 (list A$4$0 A$4$1 A$4$2 A$4$3 A$4$4))
(define-symbolic A$5$0 A$5$1 A$5$2 A$5$3 A$5$4 integer?)
(define A$5 (list A$5$0 A$5$1 A$5$2 A$5$3 A$5$4))
(define-symbolic A$6$0 A$6$1 A$6$2 A$6$3 A$6$4 integer?)
(define A$6 (list A$6$0 A$6$1 A$6$2 A$6$3 A$6$4))
(define-symbolic A$7$0 A$7$1 A$7$2 A$7$3 A$7$4 integer?)
(define A$7 (list A$7$0 A$7$1 A$7$2 A$7$3 A$7$4))
(define-symbolic A$8$0 A$8$1 A$8$2 A$8$3 A$8$4 integer?)
(define A$8 (list A$8$0 A$8$1 A$8$2 A$8$3 A$8$4))
(define A (list A$0 A$1 A$2 A$3 A$4 A$5 A$6 A$7 A$8))
(define-symbolic i integer?)


(define j_begin_ 0)

;;Functional representation of the loop body.
;;Sketch for the memoryless join: test for one instance.
(define (__loop_body__ s1 j_end_)
  (let ([s1 ($Vi_i ($Vi_i-mins s1) ($Vi_i-cmax s1))])
    (Loop j_begin_ j_end_ 5 s1
      (lambda (__s2 j)
        (let ([mins ($Vi_i-mins __s2)][cmax ($Vi_i-cmax __s2)])
           (let ([mins (list-set mins j (min (list-ref mins j)
                                         (list-ref (list-ref A 0) j)))])
              ($Vi_i
                mins
                (max (list-ref mins j) cmax))))))))

;;Wrapping for the sketch of the memoryless join.

;;-------------------------------
(define (__join__ left_state3 right_state4 j_start j_end)
  (let ([l.mins ($Vi_i-mins left_state3)][l.cmax ($Vi_i-cmax left_state3)])
     (let ([r.mins ($Vi_i-mins right_state4)]
       [r.cmax ($Vi_i-cmax right_state4)])
        (let ([loop_res (LoopFunc j_start (lambda (j) (< j j_end))
                          (lambda (j) (add1 j)) ($Vi_i
                                                  l.mins
                                                  l.cmax)
                          (lambda (type_R$Vi_i j) (let ([mins ($Vi_i-mins type_R$Vi_i)]
                                                    [cmax ($Vi_i-cmax type_R$Vi_i)])
                                                     (let ([mins (list-set mins j
                                                             (min
                                                              (list-ref mins j)
                                                              (NumExprBasic
                                                                (list-ref mins j)
                                                                (list-ref r.mins j)
                                                                (list-ref l.mins j)
                                                                1)))])
                                                        ($Vi_i
                                                          mins
                                                          (max
                                                           (list-ref mins j)
                                                           cmax))))))])
           ($Vi_i
             (choose
               ($Vi_i-mins loop_res)
               r.mins)
             (choose
               ($Vi_i-cmax loop_res)
               r.cmax))))))


;;Symbolic input state and synthesized id state
(define min_all
  (min A$0$0 A$0$1 A$0$2 A$0$3 A$0$4 A$1$0 A$1$1
             A$1$2 A$1$3 A$1$4 A$2$0 A$2$1 A$2$2 A$2$3 A$2$4 A$3$0 A$3$1
             A$3$2 A$3$3 A$3$4 A$4$0 A$4$1 A$4$2 A$4$3 A$4$4 A$5$0 A$5$1
             A$5$2 A$5$3 A$5$4 A$6$0 A$6$1 A$6$2 A$6$3 A$6$4 A$7$0 A$7$1
             A$7$2 A$7$3 A$7$4 A$8$0 A$8$1 A$8$2 A$8$3 A$8$4))

(define max_all
  (max A$0$0 A$0$1 A$0$2 A$0$3 A$0$4 A$1$0 A$1$1
             A$1$2 A$1$3 A$1$4 A$2$0 A$2$1 A$2$2 A$2$3 A$2$4 A$3$0 A$3$1
             A$3$2 A$3$3 A$3$4 A$4$0 A$4$1 A$4$2 A$4$3 A$4$4 A$5$0 A$5$1
             A$5$2 A$5$3 A$5$4 A$6$0 A$6$1 A$6$2 A$6$3 A$6$4 A$7$0 A$7$1
             A$7$2 A$7$3 A$7$4 A$8$0 A$8$1 A$8$2 A$8$3 A$8$4))


(define ($_identity iEnd) ($Vi_i (make-list 5 (choose 0 #t #f 10 -10 min_all ))
                                 (choose 0 #t #f 10 -10 min_all
                                         )))
(define-symbolic symbolic_mins$0 symbolic_mins$1 symbolic_mins$2 symbolic_mins$3 symbolic_mins$4 integer?)
(define symbolic_mins
  (list symbolic_mins$0 symbolic_mins$1 symbolic_mins$2 symbolic_mins$3 symbolic_mins$4))
(define-symbolic symbolic_cmax integer?)
(define ($_initial iEnd) ($Vi_i symbolic_mins symbolic_cmax))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list i symbolic_cmax A$0$0 A$0$1 A$0$2 A$0$3 A$0$4 A$1$0 A$1$1
             A$1$2 A$1$3 A$1$4 A$2$0 A$2$1 A$2$2 A$2$3 A$2$4 A$3$0 A$3$1
             A$3$2 A$3$3 A$3$4 A$4$0 A$4$1 A$4$2 A$4$3 A$4$4 A$5$0 A$5$1
             A$5$2 A$5$3 A$5$4 A$6$0 A$6$1 A$6$2 A$6$3 A$6$4 A$7$0 A$7$1
             A$7$2 A$7$3 A$7$4 A$8$0 A$8$1 A$8$2 A$8$3 A$8$4 symbolic_mins$0
             symbolic_mins$1 symbolic_mins$2 symbolic_mins$3 symbolic_mins$4)
  #:guarantee (assert (and
              ($Vi_i-eq? (__loop_body__ ($_initial 2) 2)
                (__join__ ($_initial 2) (__loop_body__ ($_identity 2) 2) 0 2))
              ($Vi_i-eq? (__loop_body__ ($_initial 5) 5)
                (__join__ ($_initial 5) (__loop_body__ ($_identity 5) 5) 0 5))
              ($Vi_i-eq? (__loop_body__ ($_initial 3) 3)
                (__join__ ($_initial 3) (__loop_body__ ($_identity 3) 3) 0 3))
              ($Vi_i-eq? (__loop_body__ ($_initial 4) 4)
                (__join__ ($_initial 4) (__loop_body__ ($_identity 4) 4) 0 4))))))

(if (sat? odot) (print-forms odot) (print "UNSAT"))
