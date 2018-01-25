#lang rosette

(require rosette/lib/synthax
         parsynth_racket/lib)

(current-bitwidth #f)

(define-symbolic a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))

(struct $ (cl ml c conj))
(define ($-eq? s1 s2) (and (eq? ($-cl s1) ($-cl s2))
 (eq? ($-ml s1) ($-ml s2))  (eq? ($-c s1) ($-c s2))
 (eq? ($-conj s1) ($-conj s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  (Loop i_begin_ i_end_ 10 s
    (lambda (__s i) (let ([cl ($-cl __s)] [ml ($-ml __s)] [c ($-c __s)]
      [conj ($-conj __s)])
      ($ (if (vector-ref a i) (+ cl 1) 0)
        (max ml (if (vector-ref a i) (+ cl 1) 0))
        (+ c (if (if (&& conj (vector-ref a i)) 1 0) 1 0))
        (&& conj (vector-ref a i)))))))

;;Wrapping for the sketch of the join.
(define (__join__ $L $R)
  (let ([l.cl ($-cl $L)] [l.ml ($-ml $L)] [l.c ($-c $L)] [l.conj ($-conj $L)]
    [x.cl ($-cl $R)] [x.ml ($-ml $R)] [x.c ($-c $R)] [x.conj ($-conj $R)])
    ($ (if (BoolExpr x.conj 1)
         (+ (NumExprArith l.c x.c l.ml x.ml l.cl x.cl 1)
          (NumExprArith x.c x.ml x.cl 1)) (NumExprArith x.c x.ml x.cl 1))
      (max (NumExprBasic l.c x.c l.ml x.ml l.cl x.cl 1)
       (if (BoolExpr x.conj 1)
         (+ (NumExprBasic l.c x.c l.ml x.ml l.cl x.cl 1)
          (NumExprBasic x.c x.ml x.cl 1)) (NumExprBasic x.c x.ml x.cl 1)))
      (+ (NumExprArith l.c x.c l.ml x.ml l.cl x.cl 1)
       (if
         (if (&& (BoolExpr l.conj x.conj 1) (BoolExpr x.conj 1))
           (NumExprArith x.c x.ml x.cl 1) (NumExprArith x.c x.ml x.cl 1))
         (NumExprArith x.c x.ml x.cl 1) (NumExprArith x.c x.ml x.cl 1)))
      (&& (BoolExpr l.conj x.conj 1) (BoolExpr x.conj 1)))))


;;Symbolic input state and synthesized id state
(define $_identity ($ 0 0 0 #t))
(define ($_initial _begin_ end) ($ 0 0 0 #t))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
  #:guarantee (assert (and
              ($-eq? (__loop_body__ ($_initial 0 2) 0 2 )
                (__join__ (__loop_body__ ($_initial 0 1) 0 1 ) (__loop_body__ ($_initial 1 2) 1 2 )))
              ($-eq? (__loop_body__ ($_initial 0 7) 0 7 )
                (__join__ (__loop_body__ ($_initial 0 1) 0 1 ) (__loop_body__ ($_initial 1 7) 1 7 )))
              ($-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 5) 2 5 )))
              ($-eq? (__loop_body__ ($_initial 0 8) 0 8 )
                (__join__ (__loop_body__ ($_initial 0 5) 0 5 ) (__loop_body__ ($_initial 5 8) 5 8 )))
              ($-eq? (__loop_body__ ($_initial 0 9) 0 9 )
                (__join__ (__loop_body__ ($_initial 0 3) 0 3 ) (__loop_body__ ($_initial 3 9) 3 9 )))
              ($-eq? (__loop_body__ ($_initial 0 3) 0 3 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 3) 2 3 )))
              ($-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 4) 2 4 )))))))
