#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))

(struct $ (cnt bal aux_2))
(define ($-eq? s1 s2) (and (eq? ($-cnt s1) ($-cnt s2))
                           (eq? ($-bal s1) ($-bal s2))  (eq? ($-aux_2 s1) ($-aux_2 s2))
                           ))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
  (Loop _iL_ _iR_ 10 s
        (lambda (__s i)
          (let ([cnt ($-cnt __s)] [bal ($-bal __s)]
                [aux_2 ($-aux_2 __s)])
                (let ([cnt (+ cnt (if (vector-ref a i) 1 (- 1)))])
                  ($ cnt (&& bal (>= cnt 0)) (min cnt aux_2)))))))


(define (__join__ $L $R)
  (let
      ([cnt-$L ($-cnt $L)] [bal-$L ($-bal $L)] [aux_2-$L ($-aux_2 $L)]
       [cnt-$R ($-cnt $R)] [bal-$R ($-bal $R)] [aux_2-$R ($-aux_2 $R)])

    (let ([aux_2 (min (bExpr:num->num  cnt-$L aux_2-$L cnt-$R aux_2-$R 1)
                      (bExpr:num->num  cnt-$L aux_2-$L cnt-$R aux_2-$R 1))])
      (let ([cnt (+ (bExpr:num->num  cnt-$L aux_2-$L cnt-$R aux_2-$R 1)
                    (if (bExpr:boolean  bal-$L bal-$R 1)
                        (bExpr:num->num  cnt-$L aux_2-$L cnt-$R aux_2-$R 1)
                        (bExpr:num->num  cnt-$L aux_2-$L cnt-$R aux_2-$R 1)))])
          ($ cnt
             (&& (bExpr:boolean  bal-$L bal-$R 1)
                 (bExpr:num->bool cnt-$L aux_2-$L
                                  bal-$L bal-$R cnt-$R aux_2-$R 1))
             aux_2)))))

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic aux_20 integer?)
(define $initial ($ 0 #t (choose 0 1 #t #f)))
;;Actual synthesis work happens here

(define odot
(synthesize
#:forall (list     a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
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
))))