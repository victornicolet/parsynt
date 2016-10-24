#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (flag cnt x_0))
(define ($-eq? s1 s2) (and (eq? ($-flag s1) ($-flag s2))
 (eq? ($-cnt s1) ($-cnt s2))  (eq? ($-x_0 s1) ($-x_0 s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
 (lambda (__s i)
(let ([flag ($-flag __s)] [cnt ($-cnt __s)]
      [x_0 ($-x_0 __s)])
  (let ([x_0 (vector-ref a _iL_)])
    (let ()
      ($ (vector-ref a i)
         (+ cnt (if (and (not flag) (vector-ref a i)) 1 0))
         x_0)))))))

(define (__join__ $L $R)
(let
 ([flag-$L ($-flag $L)] [cnt-$L ($-cnt $L)] [x_0-$L ($-x_0 $L)]
  [flag-$R ($-flag $R)] [cnt-$R ($-cnt $R)] [x_0-$R ($-x_0 $R)])
 (let ([x_0 (bExpr:boolean cnt-$L flag-$L x_0-$L flag-$R x_0-$R cnt-$R 1)])
 (let ()
 ($ (bExpr:num->num  cnt-$L flag-$L x_0-$L flag-$R x_0-$R cnt-$R 1)
    (+ (bExpr:num->num  cnt-$L cnt-$R 1)
       (if (bExpr:boolean  flag-$L x_0-$L flag-$R x_0-$R 1)
           (bExpr:num->num  cnt-$L cnt-$R 1)
           (bExpr:num->num  cnt-$L cnt-$R 1)))
    x_0)))))

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic x_00 flag0 boolean?)
(define-symbolic cnt0 integer?)
(define $initial ($ flag0 cnt0 (choose 0 1 #t #f)))
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
