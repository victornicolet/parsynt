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


(define-symbolic seq:#L__mtl#6$0-c$0 seq:#L__mtl#6$0-c$1 seq:#L__mtl#6$0-c$2 seq:#L__mtl#6$0-c$3 seq:#L__mtl#6$0-c$4 integer?)
(define seq:#L__mtl#6$0-c
  (list seq:#L__mtl#6$0-c$0 seq:#L__mtl#6$0-c$1 seq:#L__mtl#6$0-c$2 seq:#L__mtl#6$0-c$3 seq:#L__mtl#6$0-c$4))
(define-symbolic seq:#L__mtl#6$0-colmax$0 seq:#L__mtl#6$0-colmax$1 seq:#L__mtl#6$0-colmax$2 seq:#L__mtl#6$0-colmax$3 seq:#L__mtl#6$0-colmax$4 integer?)
(define seq:#L__mtl#6$0-colmax
  (list seq:#L__mtl#6$0-colmax$0 seq:#L__mtl#6$0-colmax$1 seq:#L__mtl#6$0-colmax$2 seq:#L__mtl#6$0-colmax$3 seq:#L__mtl#6$0-colmax$4))
(define-symbolic seq:#L__mtl#6$0-mtr integer?)
(define-symbolic seq:#L__mtl#6$0-sum integer?)
(define seq:#L__mtl#6$0
  ($Vi_Vi_ii seq:#L__mtl#6$0-c seq:#L__mtl#6$0-colmax seq:#L__mtl#6$0-mtr seq:#L__mtl#6$0-sum)
  )
(define-symbolic seq:#L__mtl#6$1-c$0 seq:#L__mtl#6$1-c$1 seq:#L__mtl#6$1-c$2 seq:#L__mtl#6$1-c$3 seq:#L__mtl#6$1-c$4 integer?)
(define seq:#L__mtl#6$1-c
  (list seq:#L__mtl#6$1-c$0 seq:#L__mtl#6$1-c$1 seq:#L__mtl#6$1-c$2 seq:#L__mtl#6$1-c$3 seq:#L__mtl#6$1-c$4))
(define-symbolic seq:#L__mtl#6$1-colmax$0 seq:#L__mtl#6$1-colmax$1 seq:#L__mtl#6$1-colmax$2 seq:#L__mtl#6$1-colmax$3 seq:#L__mtl#6$1-colmax$4 integer?)
(define seq:#L__mtl#6$1-colmax
  (list seq:#L__mtl#6$1-colmax$0 seq:#L__mtl#6$1-colmax$1 seq:#L__mtl#6$1-colmax$2 seq:#L__mtl#6$1-colmax$3 seq:#L__mtl#6$1-colmax$4))
(define-symbolic seq:#L__mtl#6$1-mtr integer?)
(define-symbolic seq:#L__mtl#6$1-sum integer?)
(define seq:#L__mtl#6$1
  ($Vi_Vi_ii seq:#L__mtl#6$1-c seq:#L__mtl#6$1-colmax seq:#L__mtl#6$1-mtr seq:#L__mtl#6$1-sum)
  )
(define-symbolic seq:#L__mtl#6$2-c$0 seq:#L__mtl#6$2-c$1 seq:#L__mtl#6$2-c$2 seq:#L__mtl#6$2-c$3 seq:#L__mtl#6$2-c$4 integer?)
(define seq:#L__mtl#6$2-c
  (list seq:#L__mtl#6$2-c$0 seq:#L__mtl#6$2-c$1 seq:#L__mtl#6$2-c$2 seq:#L__mtl#6$2-c$3 seq:#L__mtl#6$2-c$4))
(define-symbolic seq:#L__mtl#6$2-colmax$0 seq:#L__mtl#6$2-colmax$1 seq:#L__mtl#6$2-colmax$2 seq:#L__mtl#6$2-colmax$3 seq:#L__mtl#6$2-colmax$4 integer?)
(define seq:#L__mtl#6$2-colmax
  (list seq:#L__mtl#6$2-colmax$0 seq:#L__mtl#6$2-colmax$1 seq:#L__mtl#6$2-colmax$2 seq:#L__mtl#6$2-colmax$3 seq:#L__mtl#6$2-colmax$4))
(define-symbolic seq:#L__mtl#6$2-mtr integer?)
(define-symbolic seq:#L__mtl#6$2-sum integer?)
(define seq:#L__mtl#6$2
  ($Vi_Vi_ii seq:#L__mtl#6$2-c seq:#L__mtl#6$2-colmax seq:#L__mtl#6$2-mtr seq:#L__mtl#6$2-sum)
  )
(define-symbolic seq:#L__mtl#6$3-c$0 seq:#L__mtl#6$3-c$1 seq:#L__mtl#6$3-c$2 seq:#L__mtl#6$3-c$3 seq:#L__mtl#6$3-c$4 integer?)
(define seq:#L__mtl#6$3-c
  (list seq:#L__mtl#6$3-c$0 seq:#L__mtl#6$3-c$1 seq:#L__mtl#6$3-c$2 seq:#L__mtl#6$3-c$3 seq:#L__mtl#6$3-c$4))
(define-symbolic seq:#L__mtl#6$3-colmax$0 seq:#L__mtl#6$3-colmax$1 seq:#L__mtl#6$3-colmax$2 seq:#L__mtl#6$3-colmax$3 seq:#L__mtl#6$3-colmax$4 integer?)
(define seq:#L__mtl#6$3-colmax
  (list seq:#L__mtl#6$3-colmax$0 seq:#L__mtl#6$3-colmax$1 seq:#L__mtl#6$3-colmax$2 seq:#L__mtl#6$3-colmax$3 seq:#L__mtl#6$3-colmax$4))
(define-symbolic seq:#L__mtl#6$3-mtr integer?)
(define-symbolic seq:#L__mtl#6$3-sum integer?)
(define seq:#L__mtl#6$3
  ($Vi_Vi_ii seq:#L__mtl#6$3-c seq:#L__mtl#6$3-colmax seq:#L__mtl#6$3-mtr seq:#L__mtl#6$3-sum)
  )
(define-symbolic seq:#L__mtl#6$4-c$0 seq:#L__mtl#6$4-c$1 seq:#L__mtl#6$4-c$2 seq:#L__mtl#6$4-c$3 seq:#L__mtl#6$4-c$4 integer?)
(define seq:#L__mtl#6$4-c
  (list seq:#L__mtl#6$4-c$0 seq:#L__mtl#6$4-c$1 seq:#L__mtl#6$4-c$2 seq:#L__mtl#6$4-c$3 seq:#L__mtl#6$4-c$4))
(define-symbolic seq:#L__mtl#6$4-colmax$0 seq:#L__mtl#6$4-colmax$1 seq:#L__mtl#6$4-colmax$2 seq:#L__mtl#6$4-colmax$3 seq:#L__mtl#6$4-colmax$4 integer?)
(define seq:#L__mtl#6$4-colmax
  (list seq:#L__mtl#6$4-colmax$0 seq:#L__mtl#6$4-colmax$1 seq:#L__mtl#6$4-colmax$2 seq:#L__mtl#6$4-colmax$3 seq:#L__mtl#6$4-colmax$4))
(define-symbolic seq:#L__mtl#6$4-mtr integer?)
(define-symbolic seq:#L__mtl#6$4-sum integer?)
(define seq:#L__mtl#6$4
  ($Vi_Vi_ii seq:#L__mtl#6$4-c seq:#L__mtl#6$4-colmax seq:#L__mtl#6$4-mtr seq:#L__mtl#6$4-sum)
  )

(define seq:#L__mtl#6
  (list seq:#L__mtl#6$0 seq:#L__mtl#6$1 seq:#L__mtl#6$2
        seq:#L__mtl#6$3 seq:#L__mtl#6$4
        ))


;;Defining inner join function for outer loop.
(define (join#L__mtl#6 $L $R j_start j_end)
  (let ([l.c ($Vi_Vi_ii-c $L)]
        [l.colmax ($Vi_Vi_ii-colmax $L)]
        [l.mtr ($Vi_Vi_ii-mtr $L)]
        [l.sum ($Vi_Vi_ii-sum $L)]
        [r.c ($Vi_Vi_ii-c $R)]
        [r.colmax ($Vi_Vi_ii-colmax $R)]
        [r.mtr ($Vi_Vi_ii-mtr $R)]
        [r.sum ($Vi_Vi_ii-sum $R)])
    (let ([_fs_0
           (LoopFunc
            j_start
            (lambda (j) (< j j_end))
            (lambda (j) (add1 j))
            ($Vi_Vi_ii l.c l.colmax 0 0)
            (lambda (__s j)
              (let ([c ($Vi_Vi_ii-c __s)]
                    [colmax ($Vi_Vi_ii-colmax __s)]
                    [mtr ($Vi_Vi_ii-mtr __s)]
                    [sum ($Vi_Vi_ii-sum __s)])
                (let ([c (list-set
                          c
                          j
                          (+ (list-ref r.c j)
                             (list-ref c j)))])
                  (let ([colmax (list-set
                                 colmax
                                 j
                                 (max
                                  (list-ref colmax j)
                                  (list-ref c j)))])
                    ($Vi_Vi_ii c colmax
                               (max mtr (list-ref c j)) sum))))))])
      ($Vi_Vi_ii ($Vi_Vi_ii-c _fs_0) ($Vi_Vi_ii-colmax _fs_0)
                 ($Vi_Vi_ii-mtr _fs_0) r.sum))))


;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  (Loop i_begin_ i_end_ 9 s
        (lambda (__s i)
          (let ([c ($Vi_Vi_ii-c __s)]
                [colmax ($Vi_Vi_ii-colmax __s)]
                [mtr ($Vi_Vi_ii-mtr __s)]
                [sum ($Vi_Vi_ii-sum __s)])
            (let ([tup$ (join#L__mtl#6 ($Vi_Vi_ii c colmax mtr sum)
                                       (list-ref seq:#L__mtl#6 i) 0 5)])
              (let ([c ($Vi_Vi_ii-c tup$)]
                    [colmax ($Vi_Vi_ii-colmax tup$)]
                    [mtr ($Vi_Vi_ii-mtr tup$)]
                    [sum ($Vi_Vi_ii-sum tup$)])
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
                                          (list-ref r.colmax j)
                                          (list-ref r.c j)
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
               #:forall (list seq:#L__mtl#6$0-sum seq:#L__mtl#6$0-mtr
                              seq:#L__mtl#6$0-c$0 seq:#L__mtl#6$0-c$1 seq:#L__mtl#6$0-c$2
                              seq:#L__mtl#6$0-c$3 seq:#L__mtl#6$0-c$4 seq:#L__mtl#6$0-colmax$0
                              seq:#L__mtl#6$0-colmax$1 seq:#L__mtl#6$0-colmax$2
                              seq:#L__mtl#6$0-colmax$3 seq:#L__mtl#6$0-colmax$4
                              seq:#L__mtl#6$1-sum seq:#L__mtl#6$1-mtr seq:#L__mtl#6$1-c$0
                              seq:#L__mtl#6$1-c$1 seq:#L__mtl#6$1-c$2 seq:#L__mtl#6$1-c$3
                              seq:#L__mtl#6$1-c$4 seq:#L__mtl#6$1-colmax$0
                              seq:#L__mtl#6$1-colmax$1 seq:#L__mtl#6$1-colmax$2
                              seq:#L__mtl#6$1-colmax$3 seq:#L__mtl#6$1-colmax$4
                              seq:#L__mtl#6$2-sum seq:#L__mtl#6$2-mtr seq:#L__mtl#6$2-c$0
                              seq:#L__mtl#6$2-c$1 seq:#L__mtl#6$2-c$2 seq:#L__mtl#6$2-c$3
                              seq:#L__mtl#6$2-c$4 seq:#L__mtl#6$2-colmax$0
                              seq:#L__mtl#6$2-colmax$1 seq:#L__mtl#6$2-colmax$2
                              seq:#L__mtl#6$2-colmax$3 seq:#L__mtl#6$2-colmax$4
                              seq:#L__mtl#6$3-sum seq:#L__mtl#6$3-mtr seq:#L__mtl#6$3-c$0
                              seq:#L__mtl#6$3-c$1 seq:#L__mtl#6$3-c$2 seq:#L__mtl#6$3-c$3
                              seq:#L__mtl#6$3-c$4 seq:#L__mtl#6$3-colmax$0
                              seq:#L__mtl#6$3-colmax$1 seq:#L__mtl#6$3-colmax$2
                              seq:#L__mtl#6$3-colmax$3 seq:#L__mtl#6$3-colmax$4
                              seq:#L__mtl#6$4-sum seq:#L__mtl#6$4-mtr seq:#L__mtl#6$4-c$0
                              seq:#L__mtl#6$4-c$1 seq:#L__mtl#6$4-c$2 seq:#L__mtl#6$4-c$3
                              seq:#L__mtl#6$4-c$4 seq:#L__mtl#6$4-colmax$0
                              seq:#L__mtl#6$4-colmax$1 seq:#L__mtl#6$4-colmax$2
                              seq:#L__mtl#6$4-colmax$3 seq:#L__mtl#6$4-colmax$4
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
                                    ($Vi_Vi_ii-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                                                   (__join__ (__loop_body__ ($_initial 0 1) 0 1 )
                                                             (__loop_body__ ($_initial 1 5) 1 5 ) 0 5))
                                    ($Vi_Vi_ii-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                                                   (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                                             (__loop_body__ ($_initial 2 5) 2 5 ) 0 5))
                                    ($Vi_Vi_ii-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                                                   (__join__ (__loop_body__ ($_initial 0 2) 0 2 )
                                                             (__loop_body__ ($_initial 2 4) 2 4 ) 0 4))
                                    )))))

(if (sat? odot) (print-forms odot) (core odot))

;; '(define (__join__ $Vi_Vi_iiL $Vi_Vi_iiR i_start i_end)
;;    (let ((l.c ($Vi_Vi_ii-c $Vi_Vi_iiL))
;;          (l.colmax ($Vi_Vi_ii-colmax $Vi_Vi_iiL))
;;          (l.mtr ($Vi_Vi_ii-mtr $Vi_Vi_iiL))
;;          (l.sum ($Vi_Vi_ii-sum $Vi_Vi_iiL))
;;          (r.c ($Vi_Vi_ii-c $Vi_Vi_iiR))
;;          (r.colmax ($Vi_Vi_ii-colmax $Vi_Vi_iiR))
;;          (r.mtr ($Vi_Vi_ii-mtr $Vi_Vi_iiR))
;;          (r.sum ($Vi_Vi_ii-sum $Vi_Vi_iiR)))
;;      (let ((tup$
;;             (LoopFunc
;;              0
;;              (lambda (j) (< j 5))
;;              (lambda (j) (add1 j))
;;              ($Vi_Vi_ii l.c l.colmax 0 0)
;;              (lambda (__s j)
;;                (let ((c ($Vi_Vi_ii-c __s))
;;                      (colmax ($Vi_Vi_ii-colmax __s))
;;                      (mtr ($Vi_Vi_ii-mtr __s))
;;                      (sum ($Vi_Vi_ii-sum __s)))
;;                  (let ((c (list-set c j (+ (list-ref c j) (list-ref r.c j)))))
;;                    (let ((colmax
;;                           (list-set
;;                            colmax
;;                            j
;;                            (max
;;                             (+ (list-ref l.c j) (list-ref r.colmax j))
;;                             (list-ref l.colmax j)))))
;;                      ($Vi_Vi_ii c colmax (max mtr (list-ref c j)) r.sum))))))))
;;        tup$)))
