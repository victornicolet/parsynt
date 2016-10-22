#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define array (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic ind integer?)

(struct $ (flag cc x_0))

(define ($-eq? s1 s2) (and (eq? ($-flag s1) ($-flag s2))
                           (eq? ($-cc s1) ($-cc s2))  (eq? ($-x_0 s1) ($-x_0 s2))))

;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
  (Loop _iL_ _iR_ 10 s
        (lambda (__s i)
          (let ([flag ($-flag __s)] [cc ($-cc __s)]
                [x_0 ($-x_0 __s)])
            (let ([x_0 (vector-ref array _iL_)])
              (let ()
                ($ (vector-ref array ind)
                   (+ cc (if (and (not flag) (vector-ref array ind)) 1 0))
                   x_0)))))))

(define (__join__ $L $R)
  (let
      ([flag-$L ($-flag $L)] [cc-$L ($-cc $L)] [x_0-$L ($-x_0 $L)]
       [flag-$R ($-flag $R)] [cc-$R ($-cc $R)] [x_0-$R ($-x_0 $R)])
    (let ([x_0 (bExpr:boolean  x_0-$L x_0-$R 1)])
      (let ()
        ($ (bExpr:num->num  cc-$L x_0-$L cc-$R x_0-$R 1)
           (+ (bExpr:num->num  cc-$L x_0-$L cc-$R x_0-$R 1)
              (if (bExpr:boolean  x_0-$R x_0-$L flag-$L flag-$R 1)
                  (bExpr:num->num  cc-$L x_0-$L cc-$R x_0-$R 1)
                  (bExpr:num->num  cc-$L x_0-$L cc-$R x_0-$R 1)))
           x_0
           )))))

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic flag0 boolean?)
(define-symbolic x_00 cc0 integer?)
(define $initial ($ #f 0 (choose 0 1 #t #f)))
;;Actual synthesis work happens here

(define odot
  (synthesize
   #:forall (list array)
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
