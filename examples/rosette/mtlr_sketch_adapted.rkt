#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(define-symbolic a$0$0 a$0$1 a$0$2 a$0$3 a$0$4 a$0$5 a$0$6 integer?)
(define a$0 (list a$0$0 a$0$1 a$0$2 a$0$3 a$0$4 a$0$5 a$0$6))
(define a (list a$0))


(struct $ (c x mtr sum) #:transparent)
(define ($-eq? s1 s2) (and (eq? ($-c s1) ($-c s2))
                           (eq? ($-x s1) ($-x s2))
                           (eq? ($-mtr s1) ($-mtr s2))
                           (eq? ($-sum s1) ($-sum s2))
                           ))
(define j_begin_ 0)

;;Functional representation of the loop body.
;;Sketch for the memoryless join: test for one instance.
(define (__loop_body__ s j_end_)
  (let ([s ($ ($-c s) ($-x s) 0 0)])
    (Loop j_begin_ j_end_ 7 s
          (lambda (__s j)
            (let ([c ($-c __s)]
                  [x ($-x __s)]
                  [mtr ($-mtr __s)]
                  [sum ($-sum __s)])
              (let ([c (list-set c j (+ (list-ref c j)
                                        (+ sum (list-ref (list-ref a 0) j))))])
                (let ([x (list-set x j (max (list-ref c j) (list-ref x j)))])
                  ($ c
                     x
                     (max (list-ref c j) mtr)
                     (+ sum (list-ref (list-ref a 0) j))))))))))

;;Wrapping for the sketch of the memoryless join.
(define (__join__ $L $R $_start $_end)
  (let ([l.c ($-c $L)] [l.mtr ($-mtr $L)] [l.sum ($-sum $L)] [r.c ($-c $R)]
                       [l.x ($-x $L)] [r.x ($-x $R)]
                       [r.mtr ($-mtr $R)] [r.sum ($-sum $R)])
    (let ([_fs_ (LoopFunc 0 (lambda (j) (< j $_end)) (lambda (j) (add1 j))
                          ($ l.c l.x 0 0)
                          (lambda (__s j)
                            (let ([c ($-c __s)]
                                  [x ($-x __s)]
                                  [mtr ($-mtr __s)]
                                  [sum ($-sum __s)])
                              (let ([c (list-set c j (+ (list-ref c j)
                                                        (+
                                                         (NumExprArith (list-ref r.c
                                                                                 (choose (add1 j)
                                                                                         (sub1 j) j)) 1)
                                                         (NumExprArith (list-ref r.c
                                                                                 (choose (add1 j)
                                                                                         (sub1 j) j)) 1))))])
                                (let ([x (list-set x j (max
                                                        (list-ref x j)
                                                        (NumExprArith (list-ref r.c
                                                                                 (choose (add1 j)
                                                                                         (sub1 j) j))
                                                                      (list-ref c
                                                                                 (choose (add1 j)
                                                                                         (sub1 j) j))
                                                                      (list-ref r.x
                                                                                 (choose (add1 j)
                                                                                         (sub1 j) j))1)))])
                                  ($ c
                                     x
                                     (max (list-ref c j) mtr)
                                     (+ sum 0)))))))])
      ($ (choose ($-c _fs_) r.c)
         (choose ($-x _fs_) r.x)
         (choose ($-mtr _fs_) r.mtr)
         (choose ($-sum _fs_) r.sum)))))


;;Symbolic input state and synthesized id state
(define ($_identity iEnd) ($ (make-list 7 (choose 0 1 #t #f))
                             (make-list 7 (choose 0 1 #t #f))
                             (choose 0 1 #t #f 0)
                             (choose 0 1 #t #f 0)))



(define-symbolic symbolic_c$0 symbolic_c$1 symbolic_c$2
  symbolic_c$3 symbolic_c$4 symbolic_c$5 symbolic_c$6 integer?)

(define symbolic_c
  (list symbolic_c$0 symbolic_c$1 symbolic_c$2 symbolic_c$3 symbolic_c$4 symbolic_c$5 symbolic_c$6))

(define-symbolic  symbolic_x$0 symbolic_x$1 symbolic_x$2
  symbolic_x$3 symbolic_x$4 symbolic_x$5 symbolic_x$6 integer?)

(define symbolic_x
  (list symbolic_x$0 symbolic_x$1 symbolic_x$2 symbolic_x$3 symbolic_x$4 symbolic_x$5 symbolic_x$6))

(define-symbolic symbolic_mtr integer?)
(define-symbolic symbolic_sum integer?)

(define ($_initial iEnd) ($ symbolic_c symbolic_x symbolic_mtr 0))
;;Actual synthesis work happens here

(define odot (synthesize
              #:forall (list symbolic_sum symbolic_mtr
                             a$0$0 a$0$1 a$0$2 a$0$3 a$0$4 a$0$5 a$0$6
                             symbolic_c$0 symbolic_c$1 symbolic_c$2 symbolic_c$3
                             symbolic_c$4 symbolic_c$5 symbolic_c$6
                             symbolic_x$0 symbolic_x$1 symbolic_x$2
                             symbolic_x$3 symbolic_x$4 symbolic_x$5 symbolic_x$6)
              #:guarantee (assert (and
                                   ($-eq? (__loop_body__ ($_initial 2) 2)
                                          (__join__ ($_initial 2) (__loop_body__ ($_identity 2) 2) 0 2))
                                   ($-eq? (__loop_body__ ($_initial 7) 7)
                                          (__join__ ($_initial 7) (__loop_body__ ($_identity 7) 7) 0 7))
                                   ($-eq? (__loop_body__ ($_initial 5) 5)
                                          (__join__ ($_initial 5) (__loop_body__ ($_identity 5) 5) 0 5))
                                   ($-eq? (__loop_body__ ($_initial 3) 3)
                                          (__join__ ($_initial 3) (__loop_body__ ($_identity 3) 3) 0 3))
                                   ($-eq? (__loop_body__ ($_initial 4) 4)
                                          (__join__ ($_initial 4) (__loop_body__ ($_identity 4) 4) 0 4))))))

(if (sat? odot) (print-forms odot) (print "UNSAT"))
