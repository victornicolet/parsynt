#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))


(struct $ (prev is_sorted aux_0))
(define ($-eq? s1 s2) (and (eq? ($-prev s1) ($-prev s2))
                           (eq? ($-is_sorted s1) ($-is_sorted s2))
                           (eq? ($-aux_0 s1) ($-aux_0 s2))))

;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
  (Loop _iL_ _iR_ 10 s
        (lambda (__s i)
          (let ([prev ($-prev __s)]
                [is_sorted ($-is_sorted __s)]
                [aux_0 ($-aux_0 __s)])
            (let ([aux_0 (vector-ref a _iL_)])
              ($ (vector-ref a i)
                 (&& is_sorted (> (vector-ref a i) prev))
                 aux_0))))))


(define (__join__ $L $R)
  (let
      ([prev-$L ($-prev $L)]
       [is_sorted-$L ($-is_sorted $L)]
       [aux_0-$L ($-aux_0 $L)]
       [prev-$R ($-prev $R)]
       [is_sorted-$R ($-is_sorted $R)]
       [aux_0-$R ($-aux_0 $R)])

    (let ([aux_0 (bExpr:num->num  prev-$L aux_0-$L prev-$R aux_0-$R 1)])
      ($ (bExpr:num->num  prev-$L aux_0-$L prev-$R aux_0-$R 1)
         (&& (bExpr:boolean  is_sorted-$L is_sorted-$R 1)
             (bExpr:num->bool  prev-$L aux_0-$L is_sorted-$L
                               is_sorted-$R prev-$R aux_0-$R 1))
         aux_0))))

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic _min_int_ integer?)
(define $initial ($ _min_int_ #t (choose 0 1 #t #f)))

(assert (&& (< _min_int_ a$1)
            (&& (< _min_int_ a$2)
                (&& (< _min_int_ a$3)
                    (&& (< _min_int_ a$4)
                        (&& (< _min_int_ a$5)
                            (&& (< _min_int_ a$6)
                                (&& (< _min_int_ a$7)
                                    (&& (< _min_int_ a$8)
                                        (&& (< _min_int_ a$9)
                                            (< _min_int_ a$10)))))))))))
;;Actual synthesis work happens here

(define odot
  (synthesize
   #:forall (list a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
   #:guarantee (assert
                (and
                 ($-eq?
                  (__loop_body__ $initial 0 4)
                  (__join__  (__loop_body__ $initial 0 2)  (__loop_body__ $_init 2 4)))

                 ($-eq?
                  (__loop_body__ $initial 0 9)
                  (__join__  (__loop_body__ $initial 0 3)  (__loop_body__ $_init 3 9)))

                 ($-eq?
                  (__loop_body__ $initial 0 9)
                  (__join__  (__loop_body__ $initial 0 7)  (__loop_body__ $_init 7 9)))

                 ($-eq?
                  (__loop_body__ $initial 0 9)
                  (__join__  (__loop_body__ $initial 0 4)  (__loop_body__ $_init 4 9)))

                 ($-eq?
                  (__loop_body__ $initial 0 7)
                  (__join__  (__loop_body__ $initial 0 5)  (__loop_body__ $_init 5 7)))

                 ($-eq?
                  (__loop_body__ $initial 3 9)
                  (__join__  (__loop_body__ $initial 3 6)  (__loop_body__ $_init 6 9)))

                 ($-eq?
                  (__loop_body__ $initial 2 9)
                  (__join__  (__loop_body__ $initial 2 7)  (__loop_body__ $_init 7 9)))
                 ))
   ))
