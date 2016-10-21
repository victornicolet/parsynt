#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic array ind integer?)

(struct $ (flag count x_0))
(define ($-eq? s1 s2) (and (eq? ($-flag s1) ($-flag s2))
 (eq? ($-count s1) ($-count s2))  (eq? ($-x_0 s1) ($-x_0 s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
 (lambda (__s i)
   (let ([flag ($-flag __s)]
         [count ($-count __s)]
         [x_0 ($-x_0 __s)])
     (let ([x_0 (if (and (not flag) (vector-ref array _iL_)) 1 0)])
       (let ()
         ($ (vector-ref array ind)
            (+ count (if (and (not flag) (vector-ref array ind)) 1 0))
            x_0)))))))

(define (__join__ $L $R)
  (let
      ([flag-$L ($-flag $L)] [count-$L ($-count $L)] [x_0-$L ($-x_0 $L)]
       [flag-$R ($-flag $R)] [count-$R ($-count $R)] [x_0-$R ($-x_0 $R)])
    (let ([x_0 (choose x_0-$L x_0-$R)])
      (let ()
        ($ (bExpr:num->num flag-$L count-$L x_0-$L flag-$R count-$R x_0-$R 1)
           (+ (bExpr:num->num flag-$L count-$L x_0-$L flag-$R count-$R x_0-$R 1)
              (bExpr:num->num flag-$L count-$L x_0-$L flag-$R count-$R x_0-$R 1))
           x_0
           )))))

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic flag0 boolean?)
(define-symbolic x_00 count0 integer?)
(define $initial ($ #f 0 (choose 0 1 #t #f)))
;;Actual synthesis work happens here

(define odot
(synthesize
#:forall (list array ind  )
#:guarantee (assert
(and
 ($-eq?
 (__loop_body__ $initial 0 0)
(__join__  (__loop_body__ $initial 0 0)  (__loop_body__ $_init 0 0)))

($-eq?
 (__loop_body__ $initial 0 9)
(__join__  (__loop_body__ $initial 0 0)  (__loop_body__ $_init 0 9)))

($-eq?
 (__loop_body__ $initial 0 9)
(__join__  (__loop_body__ $initial 0 9)  (__loop_body__ $_init 9 9)))

($-eq?
 (__loop_body__ $initial 0 9)
(__join__  (__loop_body__ $initial 0 4)  (__loop_body__ $_init 4 9)))

($-eq?
 (__loop_body__ $initial 0 9)
(__join__  (__loop_body__ $initial 0 5)  (__loop_body__ $_init 5 9)))

($-eq?
 (__loop_body__ $initial 3 9)
(__join__  (__loop_body__ $initial 3 6)  (__loop_body__ $_init 6 9)))

($-eq?
 (__loop_body__ $initial 9 9)
(__join__  (__loop_body__ $initial 9 9)  (__loop_body__ $_init 9 9)))
))
))
