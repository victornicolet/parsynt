#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (r))
(define ($-eq? s1 s2) (and (eq? ($-r s1) ($-r s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
 (lambda (__s i)
(let ([r ($-r __s)]) ($ (modulo (+ r (if (vector-ref a i) 1 0)) 3))))))
(define (__join__ $L $R)
(let
 ([r-$L ($-r $L)] [r-$R ($-r $R)])
($ (modulo (+ (bExpr:num->num  r-$L r-$R 1) (bExpr:num->num  r-$L r-$R 1)) (bExpr:num->num  r-$L r-$R 1))))
)

;;Symbolic input state and synthesized id state
(define $_ident ($ (choose 0 1 #t #f)))
(define $_init ($ 0))
;;Actual synthesis work happens here

(define odot
(synthesize
#:forall (list i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
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
