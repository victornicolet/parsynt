#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(struct $iiVi_Vi_ (rs mlr mtr rects) #:transparent)
(define ($iiVi_Vi_-eq? s1 s2) (and (eq? ($iiVi_Vi_-rs s1) ($iiVi_Vi_-rs s2))
 (eq? ($iiVi_Vi_-mlr s1) ($iiVi_Vi_-mlr s2))
 (eq? ($iiVi_Vi_-mtr s1) ($iiVi_Vi_-mtr s2))
 (eq? ($iiVi_Vi_-rects s1) ($iiVi_Vi_-rects s2))
))



;;Defining struct for state of the inner loop.



(define-symbolic j_end integer?)
(define-symbolic j_start integer?)
(define-symbolic seq:#L__mlr#625$0-rs integer?)
(define-symbolic seq:#L__mlr#625$0-mlr integer?)
(define-symbolic seq:#L__mlr#625$0-mtr$0 seq:#L__mlr#625$0-mtr$1 seq:#L__mlr#625$0-mtr$2 seq:#L__mlr#625$0-mtr$3 seq:#L__mlr#625$0-mtr$4 integer?)
(define seq:#L__mlr#625$0-mtr
  (list seq:#L__mlr#625$0-mtr$0 seq:#L__mlr#625$0-mtr$1 seq:#L__mlr#625$0-mtr$2 seq:#L__mlr#625$0-mtr$3 seq:#L__mlr#625$0-mtr$4))
(define-symbolic seq:#L__mlr#625$0-rects$0 seq:#L__mlr#625$0-rects$1 seq:#L__mlr#625$0-rects$2 seq:#L__mlr#625$0-rects$3 seq:#L__mlr#625$0-rects$4 integer?)
(define seq:#L__mlr#625$0-rects
  (list seq:#L__mlr#625$0-rects$0 seq:#L__mlr#625$0-rects$1 seq:#L__mlr#625$0-rects$2 seq:#L__mlr#625$0-rects$3 seq:#L__mlr#625$0-rects$4))
(define seq:#L__mlr#625$0
  ($iiVi_Vi_ seq:#L__mlr#625$0-rs seq:#L__mlr#625$0-mlr seq:#L__mlr#625$0-mtr seq:#L__mlr#625$0-rects)
  )
(define-symbolic seq:#L__mlr#625$1-rs integer?)
(define-symbolic seq:#L__mlr#625$1-mlr integer?)
(define-symbolic seq:#L__mlr#625$1-mtr$0 seq:#L__mlr#625$1-mtr$1 seq:#L__mlr#625$1-mtr$2 seq:#L__mlr#625$1-mtr$3 seq:#L__mlr#625$1-mtr$4 integer?)
(define seq:#L__mlr#625$1-mtr
  (list seq:#L__mlr#625$1-mtr$0 seq:#L__mlr#625$1-mtr$1 seq:#L__mlr#625$1-mtr$2 seq:#L__mlr#625$1-mtr$3 seq:#L__mlr#625$1-mtr$4))
(define-symbolic seq:#L__mlr#625$1-rects$0 seq:#L__mlr#625$1-rects$1 seq:#L__mlr#625$1-rects$2 seq:#L__mlr#625$1-rects$3 seq:#L__mlr#625$1-rects$4 integer?)
(define seq:#L__mlr#625$1-rects
  (list seq:#L__mlr#625$1-rects$0 seq:#L__mlr#625$1-rects$1 seq:#L__mlr#625$1-rects$2 seq:#L__mlr#625$1-rects$3 seq:#L__mlr#625$1-rects$4))
(define seq:#L__mlr#625$1
  ($iiVi_Vi_ seq:#L__mlr#625$1-rs seq:#L__mlr#625$1-mlr seq:#L__mlr#625$1-mtr seq:#L__mlr#625$1-rects)
  )
(define-symbolic seq:#L__mlr#625$2-rs integer?)
(define-symbolic seq:#L__mlr#625$2-mlr integer?)
(define-symbolic seq:#L__mlr#625$2-mtr$0 seq:#L__mlr#625$2-mtr$1 seq:#L__mlr#625$2-mtr$2 seq:#L__mlr#625$2-mtr$3 seq:#L__mlr#625$2-mtr$4 integer?)
(define seq:#L__mlr#625$2-mtr
  (list seq:#L__mlr#625$2-mtr$0 seq:#L__mlr#625$2-mtr$1 seq:#L__mlr#625$2-mtr$2 seq:#L__mlr#625$2-mtr$3 seq:#L__mlr#625$2-mtr$4))
(define-symbolic seq:#L__mlr#625$2-rects$0 seq:#L__mlr#625$2-rects$1 seq:#L__mlr#625$2-rects$2 seq:#L__mlr#625$2-rects$3 seq:#L__mlr#625$2-rects$4 integer?)
(define seq:#L__mlr#625$2-rects
  (list seq:#L__mlr#625$2-rects$0 seq:#L__mlr#625$2-rects$1 seq:#L__mlr#625$2-rects$2 seq:#L__mlr#625$2-rects$3 seq:#L__mlr#625$2-rects$4))
(define seq:#L__mlr#625$2
  ($iiVi_Vi_ seq:#L__mlr#625$2-rs seq:#L__mlr#625$2-mlr seq:#L__mlr#625$2-mtr seq:#L__mlr#625$2-rects)
  )
(define-symbolic seq:#L__mlr#625$3-rs integer?)
(define-symbolic seq:#L__mlr#625$3-mlr integer?)
(define-symbolic seq:#L__mlr#625$3-mtr$0 seq:#L__mlr#625$3-mtr$1 seq:#L__mlr#625$3-mtr$2 seq:#L__mlr#625$3-mtr$3 seq:#L__mlr#625$3-mtr$4 integer?)
(define seq:#L__mlr#625$3-mtr
  (list seq:#L__mlr#625$3-mtr$0 seq:#L__mlr#625$3-mtr$1 seq:#L__mlr#625$3-mtr$2 seq:#L__mlr#625$3-mtr$3 seq:#L__mlr#625$3-mtr$4))
(define-symbolic seq:#L__mlr#625$3-rects$0 seq:#L__mlr#625$3-rects$1 seq:#L__mlr#625$3-rects$2 seq:#L__mlr#625$3-rects$3 seq:#L__mlr#625$3-rects$4 integer?)
(define seq:#L__mlr#625$3-rects
  (list seq:#L__mlr#625$3-rects$0 seq:#L__mlr#625$3-rects$1 seq:#L__mlr#625$3-rects$2 seq:#L__mlr#625$3-rects$3 seq:#L__mlr#625$3-rects$4))
(define seq:#L__mlr#625$3
  ($iiVi_Vi_ seq:#L__mlr#625$3-rs seq:#L__mlr#625$3-mlr seq:#L__mlr#625$3-mtr seq:#L__mlr#625$3-rects)
  )
(define-symbolic seq:#L__mlr#625$4-rs integer?)
(define-symbolic seq:#L__mlr#625$4-mlr integer?)
(define-symbolic seq:#L__mlr#625$4-mtr$0 seq:#L__mlr#625$4-mtr$1 seq:#L__mlr#625$4-mtr$2 seq:#L__mlr#625$4-mtr$3 seq:#L__mlr#625$4-mtr$4 integer?)
(define seq:#L__mlr#625$4-mtr
  (list seq:#L__mlr#625$4-mtr$0 seq:#L__mlr#625$4-mtr$1 seq:#L__mlr#625$4-mtr$2 seq:#L__mlr#625$4-mtr$3 seq:#L__mlr#625$4-mtr$4))
(define-symbolic seq:#L__mlr#625$4-rects$0 seq:#L__mlr#625$4-rects$1 seq:#L__mlr#625$4-rects$2 seq:#L__mlr#625$4-rects$3 seq:#L__mlr#625$4-rects$4 integer?)
(define seq:#L__mlr#625$4-rects
  (list seq:#L__mlr#625$4-rects$0 seq:#L__mlr#625$4-rects$1 seq:#L__mlr#625$4-rects$2 seq:#L__mlr#625$4-rects$3 seq:#L__mlr#625$4-rects$4))
(define seq:#L__mlr#625$4
  ($iiVi_Vi_ seq:#L__mlr#625$4-rs seq:#L__mlr#625$4-mlr seq:#L__mlr#625$4-mtr seq:#L__mlr#625$4-rects)
  )
(define-symbolic seq:#L__mlr#625$5-rs integer?)
(define-symbolic seq:#L__mlr#625$5-mlr integer?)
(define-symbolic seq:#L__mlr#625$5-mtr$0 seq:#L__mlr#625$5-mtr$1 seq:#L__mlr#625$5-mtr$2 seq:#L__mlr#625$5-mtr$3 seq:#L__mlr#625$5-mtr$4 integer?)
(define seq:#L__mlr#625$5-mtr
  (list seq:#L__mlr#625$5-mtr$0 seq:#L__mlr#625$5-mtr$1 seq:#L__mlr#625$5-mtr$2 seq:#L__mlr#625$5-mtr$3 seq:#L__mlr#625$5-mtr$4))
(define-symbolic seq:#L__mlr#625$5-rects$0 seq:#L__mlr#625$5-rects$1 seq:#L__mlr#625$5-rects$2 seq:#L__mlr#625$5-rects$3 seq:#L__mlr#625$5-rects$4 integer?)
(define seq:#L__mlr#625$5-rects
  (list seq:#L__mlr#625$5-rects$0 seq:#L__mlr#625$5-rects$1 seq:#L__mlr#625$5-rects$2 seq:#L__mlr#625$5-rects$3 seq:#L__mlr#625$5-rects$4))
(define seq:#L__mlr#625$5
  ($iiVi_Vi_ seq:#L__mlr#625$5-rs seq:#L__mlr#625$5-mlr seq:#L__mlr#625$5-mtr seq:#L__mlr#625$5-rects)
  )
(define-symbolic seq:#L__mlr#625$6-rs integer?)
(define-symbolic seq:#L__mlr#625$6-mlr integer?)
(define-symbolic seq:#L__mlr#625$6-mtr$0 seq:#L__mlr#625$6-mtr$1 seq:#L__mlr#625$6-mtr$2 seq:#L__mlr#625$6-mtr$3 seq:#L__mlr#625$6-mtr$4 integer?)
(define seq:#L__mlr#625$6-mtr
  (list seq:#L__mlr#625$6-mtr$0 seq:#L__mlr#625$6-mtr$1 seq:#L__mlr#625$6-mtr$2 seq:#L__mlr#625$6-mtr$3 seq:#L__mlr#625$6-mtr$4))
(define-symbolic seq:#L__mlr#625$6-rects$0 seq:#L__mlr#625$6-rects$1 seq:#L__mlr#625$6-rects$2 seq:#L__mlr#625$6-rects$3 seq:#L__mlr#625$6-rects$4 integer?)
(define seq:#L__mlr#625$6-rects
  (list seq:#L__mlr#625$6-rects$0 seq:#L__mlr#625$6-rects$1 seq:#L__mlr#625$6-rects$2 seq:#L__mlr#625$6-rects$3 seq:#L__mlr#625$6-rects$4))
(define seq:#L__mlr#625$6
  ($iiVi_Vi_ seq:#L__mlr#625$6-rs seq:#L__mlr#625$6-mlr seq:#L__mlr#625$6-mtr seq:#L__mlr#625$6-rects)
  )
(define-symbolic seq:#L__mlr#625$7-rs integer?)
(define-symbolic seq:#L__mlr#625$7-mlr integer?)
(define-symbolic seq:#L__mlr#625$7-mtr$0 seq:#L__mlr#625$7-mtr$1 seq:#L__mlr#625$7-mtr$2 seq:#L__mlr#625$7-mtr$3 seq:#L__mlr#625$7-mtr$4 integer?)
(define seq:#L__mlr#625$7-mtr
  (list seq:#L__mlr#625$7-mtr$0 seq:#L__mlr#625$7-mtr$1 seq:#L__mlr#625$7-mtr$2 seq:#L__mlr#625$7-mtr$3 seq:#L__mlr#625$7-mtr$4))
(define-symbolic seq:#L__mlr#625$7-rects$0 seq:#L__mlr#625$7-rects$1 seq:#L__mlr#625$7-rects$2 seq:#L__mlr#625$7-rects$3 seq:#L__mlr#625$7-rects$4 integer?)
(define seq:#L__mlr#625$7-rects
  (list seq:#L__mlr#625$7-rects$0 seq:#L__mlr#625$7-rects$1 seq:#L__mlr#625$7-rects$2 seq:#L__mlr#625$7-rects$3 seq:#L__mlr#625$7-rects$4))
(define seq:#L__mlr#625$7
  ($iiVi_Vi_ seq:#L__mlr#625$7-rs seq:#L__mlr#625$7-mlr seq:#L__mlr#625$7-mtr seq:#L__mlr#625$7-rects)
  )
(define-symbolic seq:#L__mlr#625$8-rs integer?)
(define-symbolic seq:#L__mlr#625$8-mlr integer?)
(define-symbolic seq:#L__mlr#625$8-mtr$0 seq:#L__mlr#625$8-mtr$1 seq:#L__mlr#625$8-mtr$2 seq:#L__mlr#625$8-mtr$3 seq:#L__mlr#625$8-mtr$4 integer?)
(define seq:#L__mlr#625$8-mtr
  (list seq:#L__mlr#625$8-mtr$0 seq:#L__mlr#625$8-mtr$1 seq:#L__mlr#625$8-mtr$2 seq:#L__mlr#625$8-mtr$3 seq:#L__mlr#625$8-mtr$4))
(define-symbolic seq:#L__mlr#625$8-rects$0 seq:#L__mlr#625$8-rects$1 seq:#L__mlr#625$8-rects$2 seq:#L__mlr#625$8-rects$3 seq:#L__mlr#625$8-rects$4 integer?)
(define seq:#L__mlr#625$8-rects
  (list seq:#L__mlr#625$8-rects$0 seq:#L__mlr#625$8-rects$1 seq:#L__mlr#625$8-rects$2 seq:#L__mlr#625$8-rects$3 seq:#L__mlr#625$8-rects$4))
(define seq:#L__mlr#625$8
  ($iiVi_Vi_ seq:#L__mlr#625$8-rs seq:#L__mlr#625$8-mlr seq:#L__mlr#625$8-mtr seq:#L__mlr#625$8-rects)
  )
(define seq:#L__mlr#625
  (list seq:#L__mlr#625$0 seq:#L__mlr#625$1 seq:#L__mlr#625$2 seq:#L__mlr#625$3 seq:#L__mlr#625$4 seq:#L__mlr#625$5 seq:#L__mlr#625$6 seq:#L__mlr#625$7 seq:#L__mlr#625$8))



;;Defining inner join function for outer loop.
(define (join#L__mlr#6 $L31 $R32 j_start j_end)
  (let ([l.rs ($iiVi_Vi_-rs $L31)][l.mlr ($iiVi_Vi_-mlr $L31)]
    [l.mtr ($iiVi_Vi_-mtr $L31)][l.rects ($iiVi_Vi_-rects $L31)]
    [r.rs ($iiVi_Vi_-rs $R32)][r.mlr ($iiVi_Vi_-mlr $R32)]
    [r.mtr ($iiVi_Vi_-mtr $R32)][r.rects ($iiVi_Vi_-rects $R32)])
     (let ([loop_res (LoopFunc j_start (lambda (j) (> j_end j))
                       (lambda (j) (add1 j))
                       ($iiVi_Vi_
                         0
                         l.mlr
                         l.mtr
                         l.rects)
                       (lambda (type_R$iiVi_Vi_ j) (let ([rs ($iiVi_Vi_-rs type_R$iiVi_Vi_)]
                                                     [mlr ($iiVi_Vi_-mlr type_R$iiVi_Vi_)]
                                                     [mtr ($iiVi_Vi_-mtr type_R$iiVi_Vi_)]
                                                     [rects ($iiVi_Vi_-rects type_R$iiVi_Vi_)])
                                                      (let ([rects (list-set
                                                                    rects
                                                                    j
                                                                    (+
                                                                    (list-ref rects j)
                                                                    (list-ref r.rects j)))])
                                                         (let ([mtr (list-set
                                                                    mtr
                                                                    j
                                                                    (max
                                                                    (+
                                                                    (list-ref mtr j)
                                                                    (list-ref r.rects j))
                                                                    0))])
                                                            ($iiVi_Vi_
                                                              rs
                                                              (max mlr
                                                               (list-ref mtr j))
                                                              mtr
                                                              rects))))))])
        ($iiVi_Vi_
          r.rs
          ($iiVi_Vi_-mlr loop_res)
          ($iiVi_Vi_-mtr loop_res)
          ($iiVi_Vi_-rects loop_res)))))


;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  (Loop i_begin_ i_end_ 9 s
    (lambda (__s33 i)
      (let ([rs ($iiVi_Vi_-rs __s33)][mlr ($iiVi_Vi_-mlr __s33)]
        [mtr ($iiVi_Vi_-mtr __s33)][rects ($iiVi_Vi_-rects __s33)])
         (let ([tup$24 (join#L__mlr#6 ($iiVi_Vi_
                                        rs
                                        mlr
                                        mtr
                                        rects) (list-ref seq:#L__mlr#625 i) 0 5)])
            (let ([rs ($iiVi_Vi_-rs tup$24)][mlr ($iiVi_Vi_-mlr tup$24)]
              [mtr ($iiVi_Vi_-mtr tup$24)][rects ($iiVi_Vi_-rects tup$24)])
               ($iiVi_Vi_
                 rs
                 mlr
                 mtr
                 rects)))))))

;;Wrapping for the sketch of the join.

;;-------------------------------
(define (__join__ left_state34 right_state35 i_start i_end)
  (let ([l.rs ($iiVi_Vi_-rs left_state34)]
    [l.mlr ($iiVi_Vi_-mlr left_state34)][l.mtr ($iiVi_Vi_-mtr left_state34)]
    [l.rects ($iiVi_Vi_-rects left_state34)])
     (let ([r.rs ($iiVi_Vi_-rs right_state35)]
       [r.mlr ($iiVi_Vi_-mlr right_state35)]
       [r.mtr ($iiVi_Vi_-mtr right_state35)]
       [r.rects ($iiVi_Vi_-rects right_state35)])
        (let ([tup$24 (LoopFunc j_start (lambda (j) (> j_end j))
                        (lambda (j) (add1 j))
                        ($iiVi_Vi_
                          0
                          l.mlr
                          l.mtr
                          l.rects)
                        (lambda (type_R$iiVi_Vi_ j) (let ([rs ($iiVi_Vi_-rs type_R$iiVi_Vi_)]
                                                      [mlr ($iiVi_Vi_-mlr type_R$iiVi_Vi_)]
                                                      [mtr ($iiVi_Vi_-mtr type_R$iiVi_Vi_)]
                                                      [rects ($iiVi_Vi_-rects type_R$iiVi_Vi_)])
                                                       (let ([rects (list-set
                                                                    rects
                                                                    j
                                                                    (+
                                                                    (NumExprBasic
                                                                    (list-ref rects j)
                                                                    (list-ref r.rects j)
                                                                    (list-ref l.rects j)
                                                                    (list-ref mtr j)
                                                                    (list-ref r.mtr j)
                                                                    (list-ref l.mtr j)
                                                                    1)
                                                                    (NumExprBasic
                                                                    (list-ref rects j)
                                                                    (list-ref r.rects j)
                                                                    (list-ref l.rects j)
                                                                    (list-ref mtr j)
                                                                    (list-ref r.mtr j)
                                                                    (list-ref l.mtr j)
                                                                    1)))])
                                                          (let ([mtr
                                                                  (list-set
                                                                    mtr
                                                                    j
                                                                    (max
                                                                    (+
                                                                    (NumExprBasic
                                                                    (list-ref rects j)
                                                                    (list-ref r.rects j)
                                                                    (list-ref l.rects j)
                                                                    (list-ref mtr j)
                                                                    (list-ref r.mtr j)
                                                                    (list-ref l.mtr j)
                                                                    1)
                                                                    (NumExprBasic
                                                                    (list-ref rects j)
                                                                    (list-ref r.rects j)
                                                                    (list-ref l.rects j)
                                                                    (list-ref mtr j)
                                                                    (list-ref r.mtr j)
                                                                    (list-ref l.mtr j)
                                                                    1))
                                                                    (NumExprBasic
                                                                    (list-ref rects j)
                                                                    (list-ref r.rects j)
                                                                    (list-ref l.rects j)
                                                                    (list-ref mtr j)
                                                                    (list-ref r.mtr j)
                                                                    (list-ref l.mtr j)
                                                                    mlr
                                                                    r.mlr
                                                                    l.mlr
                                                                    rs
                                                                    r.rs
                                                                    l.rs
                                                                    1)))])
                                                             ($iiVi_Vi_
                                                               rs
                                                               (max
                                                                (NumExprBasic
                                                                  (list-ref rects j)
                                                                  (list-ref r.rects j)
                                                                  (list-ref l.rects j)
                                                                  (list-ref mtr j)
                                                                  (list-ref r.mtr j)
                                                                  (list-ref l.mtr j)
                                                                  mlr
                                                                  r.mlr
                                                                  l.mlr
                                                                  rs
                                                                  r.rs
                                                                  l.rs
                                                                  1)
                                                                (NumExprBasic
                                                                  (list-ref rects j)
                                                                  (list-ref r.rects j)
                                                                  (list-ref l.rects j)
                                                                  (list-ref mtr j)
                                                                  (list-ref r.mtr j)
                                                                  (list-ref l.mtr j)
                                                                  1))
                                                               mtr
                                                               rects))))))])
           (let ([rs ($iiVi_Vi_-rs tup$24)][mlr ($iiVi_Vi_-mlr tup$24)]
             [mtr ($iiVi_Vi_-mtr tup$24)][rects ($iiVi_Vi_-rects tup$24)])
              ($iiVi_Vi_
                rs
                mlr
                mtr
                rects))))))


;;Symbolic input state and synthesized id state
(define $_identity ($iiVi_Vi_ (choose 0 #t #f 10 -10 0)
                              (choose 0 #t #f 10 -10 0)
                              (make-list 5 (choose 0 #t #f 10 -10))
                              (make-list 5 (choose 0 #t #f 10 -10))))
(define ($_initial _begin_ end)
  ($iiVi_Vi_ 0
             0
             (make-list 5 (choose 0 #t #f 10 -10))
             (make-list 5 (choose 0 #t #f 10 -10))))
;;Actual synthesis work happens here

(define odot (synthesize
  #:forall (list j_start j_end seq:#L__mlr#625$0-mlr seq:#L__mlr#625$0-rs
             seq:#L__mlr#625$0-mtr$0 seq:#L__mlr#625$0-mtr$1
             seq:#L__mlr#625$0-mtr$2 seq:#L__mlr#625$0-mtr$3
             seq:#L__mlr#625$0-mtr$4 seq:#L__mlr#625$0-rects$0
             seq:#L__mlr#625$0-rects$1 seq:#L__mlr#625$0-rects$2
             seq:#L__mlr#625$0-rects$3 seq:#L__mlr#625$0-rects$4
             seq:#L__mlr#625$1-mlr seq:#L__mlr#625$1-rs
             seq:#L__mlr#625$1-mtr$0 seq:#L__mlr#625$1-mtr$1
             seq:#L__mlr#625$1-mtr$2 seq:#L__mlr#625$1-mtr$3
             seq:#L__mlr#625$1-mtr$4 seq:#L__mlr#625$1-rects$0
             seq:#L__mlr#625$1-rects$1 seq:#L__mlr#625$1-rects$2
             seq:#L__mlr#625$1-rects$3 seq:#L__mlr#625$1-rects$4
             seq:#L__mlr#625$2-mlr seq:#L__mlr#625$2-rs
             seq:#L__mlr#625$2-mtr$0 seq:#L__mlr#625$2-mtr$1
             seq:#L__mlr#625$2-mtr$2 seq:#L__mlr#625$2-mtr$3
             seq:#L__mlr#625$2-mtr$4 seq:#L__mlr#625$2-rects$0
             seq:#L__mlr#625$2-rects$1 seq:#L__mlr#625$2-rects$2
             seq:#L__mlr#625$2-rects$3 seq:#L__mlr#625$2-rects$4
             seq:#L__mlr#625$3-mlr seq:#L__mlr#625$3-rs
             seq:#L__mlr#625$3-mtr$0 seq:#L__mlr#625$3-mtr$1
             seq:#L__mlr#625$3-mtr$2 seq:#L__mlr#625$3-mtr$3
             seq:#L__mlr#625$3-mtr$4 seq:#L__mlr#625$3-rects$0
             seq:#L__mlr#625$3-rects$1 seq:#L__mlr#625$3-rects$2
             seq:#L__mlr#625$3-rects$3 seq:#L__mlr#625$3-rects$4
             seq:#L__mlr#625$4-mlr seq:#L__mlr#625$4-rs
             seq:#L__mlr#625$4-mtr$0 seq:#L__mlr#625$4-mtr$1
             seq:#L__mlr#625$4-mtr$2 seq:#L__mlr#625$4-mtr$3
             seq:#L__mlr#625$4-mtr$4 seq:#L__mlr#625$4-rects$0
             seq:#L__mlr#625$4-rects$1 seq:#L__mlr#625$4-rects$2
             seq:#L__mlr#625$4-rects$3 seq:#L__mlr#625$4-rects$4
             seq:#L__mlr#625$5-mlr seq:#L__mlr#625$5-rs
             seq:#L__mlr#625$5-mtr$0 seq:#L__mlr#625$5-mtr$1
             seq:#L__mlr#625$5-mtr$2 seq:#L__mlr#625$5-mtr$3
             seq:#L__mlr#625$5-mtr$4 seq:#L__mlr#625$5-rects$0
             seq:#L__mlr#625$5-rects$1 seq:#L__mlr#625$5-rects$2
             seq:#L__mlr#625$5-rects$3 seq:#L__mlr#625$5-rects$4
             seq:#L__mlr#625$6-mlr seq:#L__mlr#625$6-rs
             seq:#L__mlr#625$6-mtr$0 seq:#L__mlr#625$6-mtr$1
             seq:#L__mlr#625$6-mtr$2 seq:#L__mlr#625$6-mtr$3
             seq:#L__mlr#625$6-mtr$4 seq:#L__mlr#625$6-rects$0
             seq:#L__mlr#625$6-rects$1 seq:#L__mlr#625$6-rects$2
             seq:#L__mlr#625$6-rects$3 seq:#L__mlr#625$6-rects$4
             seq:#L__mlr#625$7-mlr seq:#L__mlr#625$7-rs
             seq:#L__mlr#625$7-mtr$0 seq:#L__mlr#625$7-mtr$1
             seq:#L__mlr#625$7-mtr$2 seq:#L__mlr#625$7-mtr$3
             seq:#L__mlr#625$7-mtr$4 seq:#L__mlr#625$7-rects$0
             seq:#L__mlr#625$7-rects$1 seq:#L__mlr#625$7-rects$2
             seq:#L__mlr#625$7-rects$3 seq:#L__mlr#625$7-rects$4
             seq:#L__mlr#625$8-mlr seq:#L__mlr#625$8-rs
             seq:#L__mlr#625$8-mtr$0 seq:#L__mlr#625$8-mtr$1
             seq:#L__mlr#625$8-mtr$2 seq:#L__mlr#625$8-mtr$3
             seq:#L__mlr#625$8-mtr$4 seq:#L__mlr#625$8-rects$0
             seq:#L__mlr#625$8-rects$1 seq:#L__mlr#625$8-rects$2
             seq:#L__mlr#625$8-rects$3 seq:#L__mlr#625$8-rects$4)
  #:guarantee (assert (and
              ($iiVi_Vi_-eq? (__loop_body__ ($_initial 0 2) 0 2 )
                (__join__ (__loop_body__ ($_initial 0 1) 0 1 ) (__loop_body__ ($_initial 1 2) 1 2 ) 0 2))
              ($iiVi_Vi_-eq? (__loop_body__ ($_initial 0 7) 0 7 )
                (__join__ (__loop_body__ ($_initial 0 1) 0 1 ) (__loop_body__ ($_initial 1 7) 1 7 ) 0 7))
              ($iiVi_Vi_-eq? (__loop_body__ ($_initial 0 5) 0 5 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 5) 2 5 ) 0 5))
              ($iiVi_Vi_-eq? (__loop_body__ ($_initial 0 8) 0 8 )
                (__join__ (__loop_body__ ($_initial 0 5) 0 5 ) (__loop_body__ ($_initial 5 8) 5 8 ) 0 8))
              ($iiVi_Vi_-eq? (__loop_body__ ($_initial 0 9) 0 9 )
                (__join__ (__loop_body__ ($_initial 0 3) 0 3 ) (__loop_body__ ($_initial 3 9) 3 9 ) 0 9))
              ($iiVi_Vi_-eq? (__loop_body__ ($_initial 0 3) 0 3 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 3) 2 3 ) 0 3))
              ($iiVi_Vi_-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 4) 2 4 ) 0 4))))))

(if (sat? odot) (print-forms odot) (print "UNSAT"))
