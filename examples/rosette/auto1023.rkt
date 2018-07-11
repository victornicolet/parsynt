#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(struct $Vi_ii (colm mcols rowx) #:transparent)
(define ($Vi_ii-eq? s1 s2)
  (and
   ;; (eq? ($Vi_ii-colm s1) ($Vi_ii-colm s2))
   (eq? ($Vi_ii-mcols s1) ($Vi_ii-mcols s2))
   (eq? ($Vi_ii-rowx s1) ($Vi_ii-rowx s2))
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
(define a (list a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8))
(define-symbolic i integer?)

(define min_int
  (max  a$0$0 a$0$1 a$0$2 a$0$3 a$0$4
   a$1$0 a$1$1 a$1$2 a$1$3 a$1$4 a$2$0 a$2$1 a$2$2 a$2$3 a$2$4
   a$3$0 a$3$1 a$3$2 a$3$3 a$3$4 a$4$0 a$4$1 a$4$2 a$4$3 a$4$4
   a$5$0 a$5$1 a$5$2 a$5$3 a$5$4 a$6$0 a$6$1 a$6$2 a$6$3 a$6$4
   a$7$0 a$7$1 a$7$2 a$7$3 a$7$4 a$8$0 a$8$1 a$8$2 a$8$3 a$8$4
   )
  )



(define j_begin_ 0)

;;Functional representation of the loop body.
;;Sketch for the memoryless join: test for one instance.
(define (__loop_body__ s5 j_end_)
  (let ([s5 ($Vi_ii ($Vi_ii-colm s5) ($Vi_ii-mcols s5) 0)])
    (Loop j_begin_ j_end_ 5 s5
      (lambda (__s6 j)
        (let ([colm ($Vi_ii-colm __s6)][mcols ($Vi_ii-mcols __s6)]
          [rowx ($Vi_ii-rowx __s6)])
           (let ([colm (list-set colm j (min (list-ref colm j)
                                         (list-ref (list-ref a 0) j)))])
              ($Vi_ii
                colm
                (max (list-ref colm j) mcols)
                (max rowx (list-ref (list-ref a 0) j)))))))))

;;Wrapping for the sketch of the memoryless join.

;;-------------------------------
(define (__join__ left_state7 right_state8 j_start j_end)
  (let ([l.colm ($Vi_ii-colm left_state7)]
    [l.mcols ($Vi_ii-mcols left_state7)][l.rowx ($Vi_ii-rowx left_state7)])
     (let ([r.colm ($Vi_ii-colm right_state8)]
       [r.mcols ($Vi_ii-mcols right_state8)]
       [r.rowx ($Vi_ii-rowx right_state8)])
        (let ([loop_res (LoopFunc j_start (lambda (j) (< j j_end))
                          (lambda (j) (add1 j)) ($Vi_ii
                                                  l.colm
                                                  l.mcols
                                                  min_int)
                          (lambda (type_R$Vi_ii j) (let ([colm ($Vi_ii-colm type_R$Vi_ii)]
                                                     [mcols ($Vi_ii-mcols type_R$Vi_ii)]
                                                     [rowx ($Vi_ii-rowx type_R$Vi_ii)])
                                                      (let ([colm (list-set colm j
                                                              (min
                                                               (list-ref colm j)
                                                               (NumExprBasic
                                                                 (list-ref colm j)
                                                                 (list-ref r.colm j)
                                                                 (list-ref l.colm j)
                                                                 1)))])
                                                         ($Vi_ii
                                                           colm
                                                           (max
                                                            (list-ref colm j)
                                                            mcols)
                                                           (max rowx
                                                            (NumExprBasic
                                                              rowx
                                                              r.rowx
                                                              l.rowx
                                                              mcols
                                                              r.mcols
                                                              l.mcols
                                                              (list-ref colm j)
                                                              (list-ref r.colm j)
                                                              (list-ref l.colm j)
                                                              1)))))))])
           ($Vi_ii
             (choose
               ($Vi_ii-colm loop_res)
               r.colm)
             (choose
               ($Vi_ii-mcols loop_res)
               r.mcols)
             (choose
               ($Vi_ii-rowx loop_res)
               r.rowx))))))


;;Symbolic input state and synthesized id state

(define ($_identity iEnd) ($Vi_ii
                           (make-list 5
                                      (choose 0 #t #f 10 -10 min_int))
                           (choose 0 #t #f 10 -10 min_int)
                           (choose 0 #t #f 10 -10 0 min_int)))

(define-symbolic symbolic_colm$0 symbolic_colm$1 symbolic_colm$2 symbolic_colm$3 symbolic_colm$4 integer?)
(define symbolic_colm
  (list symbolic_colm$0 symbolic_colm$1 symbolic_colm$2 symbolic_colm$3 symbolic_colm$4))
(define-symbolic symbolic_mcols integer?)
(define-symbolic symbolic_rowx integer?)
(define ($_initial iEnd) ($Vi_ii symbolic_colm symbolic_mcols symbolic_rowx))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list i symbolic_rowx symbolic_mcols a$0$0 a$0$1 a$0$2 a$0$3 a$0$4
                 a$1$0 a$1$1 a$1$2 a$1$3 a$1$4 a$2$0 a$2$1 a$2$2 a$2$3 a$2$4
             a$3$0 a$3$1 a$3$2 a$3$3 a$3$4 a$4$0 a$4$1 a$4$2 a$4$3 a$4$4
             a$5$0 a$5$1 a$5$2 a$5$3 a$5$4 a$6$0 a$6$1 a$6$2 a$6$3 a$6$4
             a$7$0 a$7$1 a$7$2 a$7$3 a$7$4 a$8$0 a$8$1 a$8$2 a$8$3 a$8$4
             symbolic_colm$0 symbolic_colm$1 symbolic_colm$2 symbolic_colm$3
             symbolic_colm$4)
  #:guarantee (assert (and
              ($Vi_ii-eq? (__loop_body__ ($_initial 2) 2)
                (__join__ ($_initial 2) (__loop_body__ ($_identity 2) 2) 0 2))
              ($Vi_ii-eq? (__loop_body__ ($_initial 5) 5)
                (__join__ ($_initial 5) (__loop_body__ ($_identity 5) 5) 0 5))
              ($Vi_ii-eq? (__loop_body__ ($_initial 3) 3)
                (__join__ ($_initial 3) (__loop_body__ ($_identity 3) 3) 0 3))
              ($Vi_ii-eq? (__loop_body__ ($_initial 4) 4)
                (__join__ ($_initial 4) (__loop_body__ ($_identity 4) 4) 0 4))))))



(if (sat? odot) (print-forms odot) (print "UNSAT"))
