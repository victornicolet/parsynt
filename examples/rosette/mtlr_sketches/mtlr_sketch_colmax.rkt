#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

;;Defining struct for state of the inner loop.
(struct $Vi_Vi_ii (c colmax mtr sum) #:transparent)
(define ($Vi_Vi_ii-eq? s1 s2) (and (eq? ($Vi_Vi_ii-c s1) ($Vi_Vi_ii-c s2))
                                   (eq? ($Vi_Vi_ii-colmax s1) ($Vi_Vi_ii-colmax s2))
                                   (eq? ($Vi_Vi_ii-mtr s1) ($Vi_Vi_ii-mtr s2))
                                   (eq? ($Vi_Vi_ii-sum s1) ($Vi_Vi_ii-sum s2))
                                   ))

(define-symbolic a$0$0 a$0$1 a$0$2 a$0$3 a$0$4 integer?)
(define a$0 (list a$0$0 a$0$1 a$0$2 a$0$3 a$0$4))
(define-symbolic a$1$0 a$1$1 a$1$2 a$1$3 a$1$4 integer?)
(define a$1 (list a$1$0 a$1$1 a$1$2 a$1$3 a$1$4))
(define-symbolic a$2$0 a$2$1 a$2$2 a$2$3 a$2$4 integer?)
(define a$2 (list a$2$0 a$2$1 a$2$2 a$2$3 a$2$4))
(define-symbolic a$3$0 a$3$1 a$3$2 a$3$3 a$3$4 integer?)
;; (define a$3 (list a$3$0 a$3$1 a$3$2 a$3$3 a$3$4))
;; (define-symbolic a$4$0 a$4$1 a$4$2 a$4$3 a$4$4 integer?)
;; (define a$4 (list a$4$0 a$4$1 a$4$2 a$4$3 a$4$4))
;; (define-symbolic a$5$0 a$5$1 a$5$2 a$5$3 a$5$4 integer?)
;; (define a$5 (list a$5$0 a$5$1 a$5$2 a$5$3 a$5$4))
;; (define-symbolic a$6$0 a$6$1 a$6$2 a$6$3 a$6$4 integer?)
;; (define a$6 (list a$6$0 a$6$1 a$6$2 a$6$3 a$6$4))
;; (define-symbolic a$7$0 a$7$1 a$7$2 a$7$3 a$7$4 integer?)
;; (define a$7 (list a$7$0 a$7$1 a$7$2 a$7$3 a$7$4))
;; (define-symbolic a$8$0 a$8$1 a$8$2 a$8$3 a$8$4 integer?)
;; (define a$8 (list a$8$0 a$8$1 a$8$2 a$8$3 a$8$4))

(define a (list
           a$0
           a$1
           a$2
           ;; a$3
           ;; a$4
           ;; a$5
           ;; a$6
           ;; a$7
           ;; a$8
           ))


;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  (Loop i_begin_ i_end_ 9 s
        (lambda (__s i)
          (let ([c ($Vi_Vi_ii-c __s)]
                [colmax ($Vi_Vi_ii-colmax __s)]
                [mtr ($Vi_Vi_ii-mtr __s)]
                [sum ($Vi_Vi_ii-sum __s)])
            (let ([_fs_0
                   (LoopFunc
                    0
                    (lambda (j) (< j 5))
                    (lambda (j) (add1 j)) ($Vi_Vi_ii c colmax 0 0)
                    (lambda (__s j)
                      (let ([c ($Vi_Vi_ii-c __s)]
                            [colmax ($Vi_Vi_ii-colmax __s)]
                            [mtr ($Vi_Vi_ii-mtr __s)]
                            [sum ($Vi_Vi_ii-sum __s)])
                        (let
                            ([sum (+ sum (list-ref (list-ref a i) j))])
                          (let
                              ([c (list-set c j (+ (list-ref c j) sum))])
                            (let
                                ([colmax (list-set colmax j
                                                   (max (list-ref colmax j)
                                                        (list-ref c j)))])
                              ($Vi_Vi_ii
                                   c
                                   colmax
                                   (max (list-ref c j) mtr)
                                   sum)))))))])
              (let ([c ($Vi_Vi_ii-c _fs_0)]
                    [colmax ($Vi_Vi_ii-colmax _fs_0)]
                    [mtr ($Vi_Vi_ii-mtr _fs_0)]
                    [sum ($Vi_Vi_ii-sum _fs_0)])
                ($Vi_Vi_ii c colmax mtr sum)))))))

;;Wrapping for the sketch of the join.
(define (__join__ $Vi_Vi_iiL $Vi_Vi_iiR i_start i_end)
  (let ([l.c ($Vi_Vi_ii-c $Vi_Vi_iiL)]
        [l.colmax ($Vi_Vi_ii-colmax $Vi_Vi_iiL)]
        [l.mtr ($Vi_Vi_ii-mtr $Vi_Vi_iiL)]
        [l.sum ($Vi_Vi_ii-sum $Vi_Vi_iiL)]
        [r.c ($Vi_Vi_ii-c $Vi_Vi_iiR)]
        [r.colmax ($Vi_Vi_ii-colmax $Vi_Vi_iiR)]
        [r.mtr ($Vi_Vi_ii-mtr $Vi_Vi_iiR)]
        [r.sum ($Vi_Vi_ii-sum $Vi_Vi_iiR)])
    (let ([tup$ (LoopFunc
                 0
                 (lambda (j) (< j 5))
                 (lambda (j) (add1 j))
                 ($Vi_Vi_ii l.c l.colmax 0 0)
                 (lambda (__s j)
                   (let ([c ($Vi_Vi_ii-c __s)]
                         [colmax ($Vi_Vi_ii-colmax __s)]
                         [mtr ($Vi_Vi_ii-mtr __s)]
                         [sum ($Vi_Vi_ii-sum __s)])
                     (let ([c (list-set c j
                                        (+
                                         (NumExprBasic
                                          (list-ref colmax j)
                                          (list-ref r.colmax j)
                                          (list-ref l.colmax j)
                                          (list-ref c j)
                                          (list-ref r.c j)
                                          (list-ref l.c j)
                                          1)
                                         (NumExprBasic
                                          (list-ref colmax j)
                                          (list-ref r.colmax j)
                                          (list-ref l.colmax j)
                                          (list-ref c j)
                                          (list-ref r.c j)
                                          (list-ref l.c j)
                                          1))
                                        ;; (+ (list-ref c j) (list-ref r.c j))
                                        )])
                       (let ([colmax (list-set colmax j
                                        (max
                                         (NumExprBasic
                                          (list-ref colmax j)
                                          (list-ref r.colmax j)
                                          (list-ref l.colmax j)
                                          (list-ref c j)
                                          (list-ref r.c j)
                                          (list-ref l.c j)
                                          1)
                                         (NumExprBasic
                                          (list-ref colmax j)
                                          (list-ref r.colmax j)
                                          (list-ref l.colmax j)
                                          (list-ref c j)
                                          (list-ref r.c j)
                                          (list-ref l.c j)
                                          1)))
                              ;; (list-set colmax j (max (list-ref colmax j)
                              ;;                         (+ (list-ref l.c j)
                              ;;                            (list-ref r.colmax j))))
                              ])
                         ($Vi_Vi_ii c colmax
                                    ;; (max mtr (list-ref c j))
                                    (max
                                     (NumExprBasic
                                      mtr l.mtr r.mtr
                                      (list-ref colmax j)
                                      (list-ref r.colmax j)
                                      (list-ref l.colmax j)
                                      (list-ref c j)
                                      (list-ref r.c j)
                                      (list-ref l.c j)
                                      0)
                                     (NumExprBasic
                                      l.mtr r.mtr
                                      (list-ref colmax j)
                                      (list-ref r.colmax j)
                                      (list-ref l.colmax j)
                                      (list-ref c j)
                                      (list-ref r.c j)
                                      (list-ref l.c j)
                                      0))
                                    r.sum))))))])
      tup$)))



;;Symbolic input state and synthesized id state
(define $_identity ($Vi_Vi_ii (make-list 5 0)
                              (make-list 5 0) 0 0))
(define ($_initial _begin_ end)
  ($Vi_Vi_ii (make-list 5 0) (make-list 5 0) 0 0 ))
;;Actual synthesis work happens here

(define odot (time
              (synthesize
               #:forall (list a$0$0 a$0$1 a$0$2 a$0$3 a$0$4
                              a$1$0 a$1$1 a$1$2 a$1$3 a$1$4
                              a$2$0 a$2$1 a$2$2 a$2$3 a$2$4
                              ;; a$3$0 a$3$1 a$3$2 a$3$3 a$3$4
                              ;; a$4$0 a$4$1 a$4$2 a$4$3 a$4$4
                              ;; a$5$0 a$5$1 a$5$2 a$5$3 a$5$4
                              ;; a$6$0 a$6$1 a$6$2 a$6$3 a$6$4
                              ;; a$7$0 a$7$1 a$7$2 a$7$3 a$7$4
                              ;; a$8$0 a$8$1 a$8$2 a$8$3 a$8$4
                         )
               #:guarantee (assert (and
                                    ($Vi_Vi_ii-eq? (__loop_body__
                                                    ($_initial 0 2) 0 2 )
                                                   (__join__ (__loop_body__ ($_initial 0 1) 0 1 )
                                                             (__loop_body__ ($_initial 1 2) 1 2 ) 0 2))
                                    ($Vi_Vi_ii-eq? (__loop_body__
                                                    ($_initial 0 3) 0 3)
                                                   (__join__ (__loop_body__ ($_initial 0 2) 0 2)
                                                             (__loop_body__ ($_initial 2 3) 2 3) 0 3))
                                    ;; ($Vi_Vi_ii-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                                    ;;                (__join__ (__loop_body__ ($_initial 0 1) 0 1 )
                                    ;;                          (__loop_body__ ($_initial 1 5) 1 5 ) 0 5))
                                    ;; ($Vi_Vi_ii-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                                    ;;                (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                    ;;                          (__loop_body__ ($_initial 2 5) 2 5 ) 0 5))
                                    ;; ($Vi_Vi_ii-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                                    ;;                (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                    ;;                          (__loop_body__ ($_initial 2 4) 2 4 ) 0 4))
                                    )))))

(if (sat? odot) (print-forms odot) (core odot))
