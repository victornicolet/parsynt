#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))

(struct $ (f c aux_1))
(define ($-eq? s1 s2) (and (eq? ($-f s1) ($-f s2))  (eq? ($-c s1) ($-c s2))
                           (eq? ($-aux_1 s1) ($-aux_1 s2))))

;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
  (Loop _iL_ _iR_ 10 s
        (lambda (__s i)
          (let ([f ($-f __s)] [c ($-c __s)]
                [aux_1 ($-aux_1 __s)])
            (let ([aux_1 (if (> (vector-ref a i) 0) (add1 aux_1) aux_1)])
              ($ (|| f (= (vector-ref a i) 0))
                 (+ c (if (&& f (> (vector-ref a i) 0)) 1 0)) aux_1))))))

(define (__join__ $L $R)
  (let
      ([f-$L ($-f $L)]
       [c-$L ($-c $L)]
       [aux_1-$L ($-aux_1 $L)]
       [f-$R ($-f $R)]
       [c-$R ($-c $R)]
       [aux_1-$R ($-aux_1 $R)])
    (let ([aux_1 (+ (bExpr:num->num  c-$L c-$R aux_1-$R aux_1-$L 1)
                    (bExpr:num->num aux_1-$R aux_1-$L c-$L c-$R 1))])
      ($ (|| (bExpr:boolean  f-$L f-$R 1)
             (bExpr:num->bool  c-$L f-$L aux_1-$L f-$R aux_1-$R c-$R 1))
         (+ (bExpr:num->num  c-$L c-$R aux_1-$L aux_1-$R 1)
            (if (&&
                 (bExpr:boolean  f-$L f-$R 1)
                 (bExpr:num->bool  c-$L f-$L aux_1-$L f-$R aux_1-$R c-$R 1))
                (bExpr:num->num  c-$L c-$R aux_1-$L aux_1-$R 1)
                (bExpr:num->num  c-$L c-$R aux_1-$L aux_1-$R 1)))
         aux_1)))
)

;;Symbolic input state and synthesized id state
(define $_ident ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic aux_10 integer?)
(define $_init ($ #f 0 (choose 0 1 #t #f)))
;;Actual synthesis work happens here

(define odot
(synthesize
#:forall (list a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
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

(print-forms odot)

;; '(define (__join__ $L $R)
;;    (let ((f-$L ($-f $L))
;;          (c-$L ($-c $L))
;;          (aux_1-$L ($-aux_1 $L))
;;          (f-$R ($-f $R))
;;          (c-$R ($-c $R))
;;          (aux_1-$R ($-aux_1 $R)))
;;      (let ((aux_1 (+ (add1 aux_1-$R) (sub1 aux_1-$L))))
;;        ($
;;         (|| (|| f-$L f-$R) (! (= 0 (- c-$R c-$L))))
;;         (+
;;          (min c-$L aux_1-$R)
;;          (if (&& (! f-$L) (identity (>= 8 (sub1 8))))
;;            c-$R
;;            (max aux_1-$R c-$L)))
;;         aux_1))))
;; Can be transformed to simpler join :
;; '(define (__join__ $L $R)
;;    (let ((f-$L ($-f $L))
;;          (c-$L ($-c $L))
;;          (aux_1-$L ($-aux_1 $L))
;;          (f-$R ($-f $R))
;;          (c-$R ($-c $R))
;;          (aux_1-$R ($-aux_1 $R)))
;;      (let ((aux_1 (+ aux_1-$R aux_1-$L)))
;;        ($
;;         (|| (|| f-$L f-$R) (! (= 0 (- c-$R c-$L))))
;;         (+
;;          (min c-$L aux_1-$R)
;;          (if (! f-$L)
;;            c-$R
;;            (max aux_1-$R c-$L)))
;;         aux_1))))
