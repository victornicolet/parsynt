#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
 (define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
;;(define a (vector #t #f #t #f #t #f #f #f #f #t))
(define-symbolic i integer?)

(struct $ (max_d cur_l conj pre_l))
(define ($-eq? s1 s2) (and (eq? ($-max_d s1) ($-max_d s2))
                           (eq? ($-cur_l s1) ($-cur_l s2))
                           (eq? ($-conj s1) ($-conj s2))
                           (eq? ($-pre_l s1) ($-pre_l s2))))


;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
  (Loop _iL_ _iR_ 10 s
        (lambda (__s i)
          (let ([max_d ($-max_d __s)]
                [cur_l ($-cur_l __s)]
                [conj ($-conj __s)]
                [pre_l ($-pre_l __s)])
            (let ([conj (&& conj (! (vector-ref a i)))])
              ($ (if (vector-ref a i) (max max_d cur_l) max_d)
                 (if (vector-ref a i) 0 (+ cur_l 1))
                 conj
                 (+ pre_l (if conj 1 0))))))))

(define (__join__ $L $R)
  (let
      ([max_d-$L ($-max_d $L)] [cur_l-$L ($-cur_l $L)] [conj-$L ($-conj $L)]
       [pre_l-$L ($-pre_l $L)] [max_d-$R ($-max_d $R)] [cur_l-$R ($-cur_l $R)]
       [conj-$R ($-conj $R)] [pre_l-$R ($-pre_l $R)])
    ($ (if
        (bExpr:num->bool  max_d-$L cur_l-$L pre_l-$L max_d-$R cur_l-$R pre_l-$R 1)
        (bExpr:num->num  max_d-$L cur_l-$L pre_l-$L max_d-$R cur_l-$R pre_l-$R 1)
        (bExpr:num->num  max_d-$L cur_l-$L pre_l-$L max_d-$R cur_l-$R pre_l-$R 1))
       (if (bExpr:boolean  conj-$L conj-$R 1)
           (bExpr:num->num  max_d-$L cur_l-$L pre_l-$L max_d-$R cur_l-$R pre_l-$R 1)
           (bExpr:num->num  max_d-$L cur_l-$L pre_l-$L max_d-$R cur_l-$R pre_l-$R 1))
       (bExpr:boolean  conj-$L conj-$R 1)
       (bExpr:num->num  max_d-$L cur_l-$L pre_l-$L max_d-$R cur_l-$R pre_l-$R 1))))


;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1)
                  (choose 0 1)
                  (choose #t #f)
                  (choose 0 1)))

(define $initial ($ 0 0 #t 0))
;;Actual synthesis work happens here

(define odot
  (synthesize
   #:forall (list i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
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
