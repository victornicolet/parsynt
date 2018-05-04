#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(define-symbolic a$0$0 a$0$1 a$0$2 a$0$3 a$0$4 integer?)
(define a$0 (list a$0$0 a$0$1 a$0$2 a$0$3 a$0$4))
(define a (list a$0))
(define-symbolic i integer?)

(struct $ (c mtr sum) #:transparent)
(define ($-eq? s1 s2) (and (eq? ($-c s1) ($-c s2))
 (eq? ($-mtr s1) ($-mtr s2))  (eq? ($-sum s1) ($-sum s2))
))
(define j_begin_ 0)

;;Functional representation of the loop body.
;;Sketch for the memoryless join: test for one instance.
(define (__loop_body__ s j_end_)
  (let ([s ($ ($-c s) 0 0)])
    (Loop j_begin_ j_end_ 5 s
      (lambda (__s j) (let ([c ($-c __s)] [mtr ($-mtr __s)]
        [sum ($-sum __s)])
        (let ([c (list-set c j (+ (list-ref c j)
                                (+ sum (list-ref (list-ref a 0) j))))])
           ($ c (max (list-ref c j) mtr) (+ sum (list-ref (list-ref a 0) j)))))))))

;;Wrapping for the sketch of the memoryless join.
(define (__join__ $L $R)
  (let ([l.c ($-c $L)] [l.mtr ($-mtr $L)] [l.sum ($-sum $L)] [r.c ($-c $R)]
    [r.mtr ($-mtr $R)] [r.sum ($-sum $R)])
    (let
        ([s (LoopFunc 0 (lambda (j) (< j 5)) (lambda (j) (add1 j)) ($ l.c 0 0)
      (lambda (__s j) (let ([c ($-c __s)][mtr ($-mtr __s)][sum ($-sum __s)])
                         (let ([c (list-set c j (+ (list-ref c j)
                                                 (+
                                                  (NumExprArith (list-ref r.c (choose (add1 j) (sub1 j) j)) 1)
                                                  (NumExprArith (list-ref r.c (choose (add1 j) (sub1 j) j)) 1))))])
                            ($ c (max (list-ref c j) mtr)
                              (+ sum
                               (NumExprArith r.sum
                                 r.mtr
                                 (list-ref r.c (choose (add1 j) (sub1 j) j)) 1)))))))])
      ($ ($-c s) (choose ($-mtr s) r.mtr) (choose ($-sum s) r.sum)))))


;;Symbolic input state and synthesized id state
(define ($_identity iEnd) ($ (make-list 5 (choose 0 1 #t #f)) (choose 0 1 #t #f 0) (choose 0 1 #t #f 0)))
(define-symbolic symbolic_c$0 symbolic_c$1 symbolic_c$2 symbolic_c$3 symbolic_c$4 integer?)
(define symbolic_c
  (list symbolic_c$0 symbolic_c$1 symbolic_c$2 symbolic_c$3 symbolic_c$4))
(define-symbolic symbolic_mtr integer?)
(define-symbolic symbolic_sum integer?)
(define ($_initial iEnd) ($ symbolic_c symbolic_mtr symbolic_sum))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list i a$0$0 a$0$1 a$0$2 a$0$3 a$0$4)
  #:guarantee (assert (and
              ($-eq? (__loop_body__ ($_initial 2) 2)
                (__join__ ($_initial 2) (__loop_body__ ($_identity 2) 2)))
              ($-eq? (__loop_body__ ($_initial 7) 7)
                (__join__ ($_initial 7) (__loop_body__ ($_identity 7) 7)))
              ($-eq? (__loop_body__ ($_initial 5) 5)
                (__join__ ($_initial 5) (__loop_body__ ($_identity 5) 5)))
              ($-eq? (__loop_body__ ($_initial 8) 8)
                (__join__ ($_initial 8) (__loop_body__ ($_identity 8) 8)))
              ($-eq? (__loop_body__ ($_initial 9) 9)
                (__join__ ($_initial 9) (__loop_body__ ($_identity 9) 9)))
              ($-eq? (__loop_body__ ($_initial 3) 3)
                (__join__ ($_initial 3) (__loop_body__ ($_identity 3) 3)))
              ($-eq? (__loop_body__ ($_initial 4) 4)
                (__join__ ($_initial 4) (__loop_body__ ($_identity 4) 4)))))))

(if (sat? odot)
    (print-forms odot)
    (print "UNSAT"))
