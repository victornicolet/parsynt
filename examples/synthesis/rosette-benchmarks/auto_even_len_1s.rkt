#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic tmp i integer?)

(struct $ (f g tf aux_0 aux_1))
(define ($-eq? s1 s2) (and (eq? ($-f s1) ($-f s2))  (eq? ($-g s1) ($-g s2))
                           (eq? ($-tf s1) ($-tf s2))  (eq? ($-aux_0 s1) ($-aux_0 s2))
                           (eq? ($-aux_1 s1) ($-aux_1 s2))
                           ))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
  (Loop _iL_ _iR_ 10 s
        (lambda (__s i)
          (let ([f ($-f __s)] [g ($-g __s)] [tf ($-tf __s)] [aux_0 ($-aux_0 __s)]
                [aux_1 ($-aux_1 __s)])
            (let ([aux_0 (vector-ref a _iL_)]
                  [aux_1 (not (vector-ref a _iL_))])
              ($ (|| (&& (not (vector-ref a i)) f) (&& (not f) (&& (not g) (vector-ref a i))))
                 (not f) f aux_0 aux_1))))))


(define (__join__ $L $R)
  (let
      ([f-$L ($-f $L)] [g-$L ($-g $L)] [tf-$L ($-tf $L)] [aux_0-$L ($-aux_0 $L)]
       [aux_1-$L ($-aux_1 $L)] [f-$R ($-f $R)] [g-$R ($-g $R)] [tf-$R ($-tf $R)]
       [aux_0-$R ($-aux_0 $R)] [aux_1-$R ($-aux_1 $R)])
    (let ([aux_0 (bExpr:boolean  f-$L g-$L tf-$L aux_0-$L aux_1-$L f-$R g-$R tf-$R aux_0-$R aux_1-$R 1)]
          [aux_1 (bExpr:boolean  f-$L g-$L tf-$L aux_0-$L aux_1-$L f-$R g-$R tf-$R aux_0-$R aux_1-$R 1)])
      ($ (|| (bExpr:boolean  f-$L g-$L tf-$L aux_0-$L aux_1-$L f-$R g-$R tf-$R aux_0-$R aux_1-$R 1)
             (&& (bExpr:boolean  f-$L g-$L tf-$L aux_0-$L aux_1-$L f-$R g-$R tf-$R aux_0-$R aux_1-$R 1)
                 (bExpr:boolean  f-$L g-$L tf-$L aux_0-$L aux_1-$L f-$R g-$R tf-$R aux_0-$R aux_1-$R 1)))
         (bExpr:boolean  f-$L g-$L tf-$L aux_0-$L aux_1-$L f-$R g-$R tf-$R aux_0-$R aux_1-$R 1)
         (bExpr:boolean  f-$L g-$L tf-$L aux_0-$L aux_1-$L f-$R g-$R tf-$R aux_0-$R aux_1-$R 1)
         aux_0 aux_1))))

;;Symbolic input state and synthesized id state
(define $_ident ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic aux_10 aux_00 boolean?)
(define $_init ($ #t #f #t (choose 0 1 #t #f) (choose 0 1 #t #f)))
;;Actual synthesis work happens here

(define odot
  (synthesize
   #:forall (list tmp i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
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
   ))
