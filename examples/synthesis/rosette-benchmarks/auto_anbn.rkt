#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(current-bitwidth #f)
(define-symbolic ar$1 ar$2 ar$3 ar$4 ar$5 ar$6 ar$7 ar$8 ar$9 ar$10 integer?)
(define ar (vector ar$1 ar$2 ar$3 ar$4 ar$5 ar$6 ar$7 ar$8 ar$9 ar$10))

(define-symbolic a b integer?)

(struct $ (bn an a_left b_left))
(define ($-eq? s1 s2) (and (eq? ($-bn s1) ($-bn s2))
 (eq? ($-an s1) ($-an s2))  (eq? ($-a_left s1) ($-a_left s2))
 (eq? ($-b_left s1) ($-b_left s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
  (Loop _iL_ _iR_ 10 s
        (lambda (__s i)
          (let ([bn ($-bn __s)] [an ($-an __s)] [a_left ($-a_left __s)]
                [b_left ($-b_left __s)])
            (let ([a_left (= (vector-ref ar _iL_) a)]
                  [b_left (= (vector-ref ar _iL_) b)])
              (let ([an (&& (= (vector-ref ar i) a) an)])
                ($ (&& (|| (= (vector-ref ar i) b) an) bn)
                   an a_left b_left)))))))

(define (__join__ $L $R)
  (let
      ([bn-$L ($-bn $L)] [an-$L ($-an $L)] [a_left-$L ($-a_left $L)]
       [b_left-$L ($-b_left $L)] [bn-$R ($-bn $R)] [an-$R ($-an $R)]
       [a_left-$R ($-a_left $R)] [b_left-$R ($-b_left $R)])

    (let ([a_left (bExpr:boolean  bn-$L an-$L a_left-$L b_left-$L bn-$R an-$R
                                 a_left-$R b_left-$R 1)]
          [b_left (bExpr:boolean  bn-$L an-$L a_left-$L b_left-$L
                                 bn-$R an-$R a_left-$R b_left-$R 1)])

      (let ([an (&& (bExpr:boolean   bn-$L an-$L a_left-$L b_left-$L bn-$R
                                     an-$R a_left-$R b_left-$R  1)
                    (bExpr:boolean  bn-$L an-$L a_left-$L b_left-$L bn-$R
                                    an-$R a_left-$R b_left-$R 1))])
        ($ (&&
            (|| (bExpr:boolean   bn-$L an-$L a_left-$L b_left-$L
                                 bn-$R an-$R a_left-$R b_left-$R  1)
                (bExpr:boolean  bn-$L an-$L a_left-$L b_left-$L
                                bn-$R an-$R a_left-$R b_left-$R 1))
            (bExpr:boolean  bn-$L an-$L a_left-$L b_left-$L
                            bn-$R an-$R a_left-$R b_left-$R 1))
           an a_left b_left))))
  )

;;Symbolic input state and synthesized id state
(define $_ident ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic b_left0 a_left0 boolean?)
(define $_init ($ #t #t (choose 0 1 #t #f) (choose 0 1 #t #f)))
;;Actual synthesis work happens here

(define odot
  (time
   (synthesize
    #:forall (list a b ar$1 ar$2 ar$3 ar$4 ar$5 ar$6 ar$7 ar$8 ar$9 ar$10)
    #:guarantee (assert
                 (and
                  ($-eq?
                   (__loop_body__ $_init 0 4)
                   (__join__  (__loop_body__ $_init 0 2)  (__loop_body__ $_init 2 4)))

                  ($-eq?
                   (__loop_body__ $_init 0 9)
                   (__join__  (__loop_body__ $_init 0 3)  (__loop_body__ $_init 3 9)))

                  ($-eq?
                   (__loop_body__ $_init 0 9)
                   (__join__  (__loop_body__ $_init 0 7)  (__loop_body__ $_init 7 9)))

                  ($-eq?
                   (__loop_body__ $_init 0 9)
                   (__join__  (__loop_body__ $_init 0 4)  (__loop_body__ $_init 4 9)))

                  ($-eq?
                   (__loop_body__ $_init 0 7)
                   (__join__  (__loop_body__ $_init 0 5)  (__loop_body__ $_init 5 7)))

                  ($-eq?
                   (__loop_body__ $_init 3 9)
                   (__join__  (__loop_body__ $_init 3 6)  (__loop_body__ $_init 6 9)))

                  ($-eq?
                   (__loop_body__ $_init 2 9)
                   (__join__  (__loop_body__ $_init 2 7)  (__loop_body__ $_init 7 9)))
                  ))
    )))

(print-forms odot)
