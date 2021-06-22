#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(struct $b (b) #:transparent)
(define ($b-eq? s1 s2) (and (eq? ($b-b s1) ($b-b s2))))

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
(define (__loop_body__ s j_end_)
  (let ([s ($b #t)])
    (Loop j_begin_ j_end_ 5 s
      (lambda (__s j)
        (let ([b ($b-b __s)])
           ($b
             (&& b
              (> (list-ref (list-ref A 1) j)
               (list-ref (list-ref A (- 1 1)) j)))))))))

;;Wrapping for the sketch of the memoryless join.

;;-------------------------------
(define (__join__ left_state right_state j_start j_end)
  (let ([l.b ($b-b left_state)])
     (let ([r.b ($b-b right_state)])
        ($b
          (&& (BoolExpr l.b r.b 0) (BoolExpr r.b r.b 0))))))


;;Symbolic input state and synthesized id state
(define ($_identity iEnd) ($b (choose 0 #t #f 10 -10 #t)))
(define-symbolic symbolic_b boolean?)
(define ($_initial iEnd) ($b symbolic_b))
;;Actual synthesis work happens here

(define odot
  (time
   (synthesize
    #:forall (list i symbolic_b A$0$0 A$0$1 A$0$2 A$0$3 A$0$4 A$1$0 A$1$1 A$1$2
                   A$1$3 A$1$4 A$2$0 A$2$1 A$2$2 A$2$3 A$2$4 A$3$0 A$3$1 A$3$2
                   A$3$3 A$3$4 A$4$0 A$4$1 A$4$2 A$4$3 A$4$4 A$5$0 A$5$1 A$5$2
                   A$5$3 A$5$4 A$6$0 A$6$1 A$6$2 A$6$3 A$6$4 A$7$0 A$7$1 A$7$2
                   A$7$3 A$7$4 A$8$0 A$8$1 A$8$2 A$8$3 A$8$4)
    #:guarantee (assert (and
                         ($b-eq? (__loop_body__ ($_initial 2) 2)
                                 (__join__ ($_initial 2) (__loop_body__ ($_identity 2) 2) 0 2))
                         ($b-eq? (__loop_body__ ($_initial 5) 5)
                                 (__join__ ($_initial 5) (__loop_body__ ($_identity 5) 5) 0 5))
                         ($b-eq? (__loop_body__ ($_initial 3) 3)
                                 (__join__ ($_initial 3) (__loop_body__ ($_identity 3) 3) 0 3))
                         ($b-eq? (__loop_body__ ($_initial 4) 4)
                                 (__join__ ($_initial 4) (__loop_body__ ($_identity 4) 4) 0 4)))))))

(if (sat? odot) (print-forms odot) (print "UNSAT"))
