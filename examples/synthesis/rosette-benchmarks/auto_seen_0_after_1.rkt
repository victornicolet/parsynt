#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (seen1 r aux_2))
(define ($-eq? s1 s2) (and (eq? ($-seen1 s1) ($-seen1 s2))
 (eq? ($-r s1) ($-r s2))  (eq? ($-aux_2 s1) ($-aux_2 s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
 (lambda (__s i)
(let ([seen1 ($-seen1 __s)] [r ($-r __s)]
      [aux_2 ($-aux_2 __s)])
  (let ([aux_2 (|| (! (vector-ref a i)) aux_2)])
    (let ()
      ($ (|| seen1 (vector-ref a i))
         (|| (&& seen1 (! (vector-ref a i))) r)
         aux_2)))))))

(define (__join__ $L $R)
(let
 ([seen1-$L ($-seen1 $L)] [r-$L ($-r $L)] [aux_2-$L ($-aux_2 $L)]
  [seen1-$R ($-seen1 $R)] [r-$R ($-r $R)] [aux_2-$R ($-aux_2 $R)])
 (let ([aux_2
        (|| (bExpr:boolean  seen1-$L r-$L aux_2-$L seen1-$R r-$R aux_2-$R 1)
            (bExpr:boolean  seen1-$L r-$L aux_2-$L seen1-$R r-$R aux_2-$R 1))])
   (let ()
     ($ (||
         (bExpr:boolean  seen1-$L r-$L aux_2-$L seen1-$R r-$R aux_2-$R 1)
         (bExpr:boolean  seen1-$L r-$L aux_2-$L seen1-$R r-$R aux_2-$R 1))

        (|| (bExpr:boolean  seen1-$L r-$L aux_2-$L seen1-$R r-$R aux_2-$R 1)
            (bExpr:boolean  seen1-$L r-$L aux_2-$L seen1-$R r-$R aux_2-$R 1))

        aux_2)))))

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic aux_20 boolean?)
(define $initial ($ #f #f (choose 0 1 #t #f)))
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
