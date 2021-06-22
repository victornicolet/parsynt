#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(struct $Vi_i (colsum boxsum) #:transparent)
(define ($Vi_i-eq? s1 s2) (and (eq? ($Vi_i-colsum s1) ($Vi_i-colsum s2))
 (eq? ($Vi_i-boxsum s1) ($Vi_i-boxsum s2))
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


(define j_begin_ 0)

;;Functional representation of the loop body.
;;Sketch for the memoryless join: test for one instance.
(define (__loop_body__ s j_end_)
  (let ([s ($Vi_i ($Vi_i-colsum s) 0)])
    (Loop j_begin_ j_end_ 5 s
      (lambda (__s j)
        (let ([colsum ($Vi_i-colsum __s)][boxsum ($Vi_i-boxsum __s)])
           (let ([colsum (list-set colsum j (+ (list-ref colsum j)
                                             (list-ref (list-ref a 3) j)))])
              ($Vi_i
                colsum
                (if (<= j 3) (+ boxsum (list-ref colsum j)) boxsum))))))))

;;Wrapping for the sketch of the memoryless join.

;;-------------------------------
(define (__join__ left_state right_state j_start j_end)
  (let ([l.colsum ($Vi_i-colsum left_state)]
    [l.boxsum ($Vi_i-boxsum left_state)])
     (let ([r.colsum ($Vi_i-colsum right_state)]
       [r.boxsum ($Vi_i-boxsum right_state)])
        (let ([loop_res (LoopFunc j_start (lambda (j) (< j j_end))
                          (lambda (j) (add1 j)) ($Vi_i
                                                  l.colsum
                                                  0)
                          (lambda (type_R$Vi_i j) (let ([colsum ($Vi_i-colsum type_R$Vi_i)]
                                                    [boxsum ($Vi_i-boxsum type_R$Vi_i)])
                                                     (let ([colsum (list-set colsum j
                                                             (+
                                                              (list-ref colsum j)
                                                              (NumExprArith
                                                                (list-ref colsum j)
                                                                (list-ref r.colsum j)
                                                                (list-ref l.colsum j)
                                                                0)))])
                                                        ($Vi_i
                                                          colsum
                                                          (if
                                                            (BoolExprCompar
                                                              boxsum
                                                              r.boxsum
                                                              l.boxsum
                                                              (list-ref colsum j)
                                                              (list-ref r.colsum j)
                                                              (list-ref l.colsum j)
                                                              1)
                                                            (+ boxsum
                                                             (list-ref colsum j))
                                                            boxsum))))))])
           ($Vi_i
             (choose
               ($Vi_i-colsum loop_res)
               r.colsum)
             (choose
               ($Vi_i-boxsum loop_res)
               r.boxsum))))))


;;Symbolic input state and synthesized id state
(define ($_identity iEnd) ($Vi_i (make-list 5 (choose 0 #t #f 10 -10)) (choose 0 #t #f 10 -10 0)))
(define-symbolic symbolic_colsum$0 symbolic_colsum$1 symbolic_colsum$2 symbolic_colsum$3 symbolic_colsum$4 integer?)
(define symbolic_colsum
  (list symbolic_colsum$0 symbolic_colsum$1 symbolic_colsum$2 symbolic_colsum$3 symbolic_colsum$4))
(define-symbolic symbolic_boxsum integer?)
(define ($_initial iEnd) ($Vi_i symbolic_colsum symbolic_boxsum))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list i symbolic_boxsum a$0$0 a$0$1 a$0$2 a$0$3 a$0$4 a$1$0 a$1$1
             a$1$2 a$1$3 a$1$4 a$2$0 a$2$1 a$2$2 a$2$3 a$2$4 a$3$0 a$3$1
             a$3$2 a$3$3 a$3$4 a$4$0 a$4$1 a$4$2 a$4$3 a$4$4 a$5$0 a$5$1
             a$5$2 a$5$3 a$5$4 a$6$0 a$6$1 a$6$2 a$6$3 a$6$4 a$7$0 a$7$1
             a$7$2 a$7$3 a$7$4 a$8$0 a$8$1 a$8$2 a$8$3 a$8$4
             symbolic_colsum$0 symbolic_colsum$1 symbolic_colsum$2
             symbolic_colsum$3 symbolic_colsum$4)
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
