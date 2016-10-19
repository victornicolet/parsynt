#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (mts___0 aux0))
(define ($-eq? s1 s2) (and (eq? ($-mts___0 s1) ($-mts___0 s2))
                           (eq? ($-aux0 s1) ($-aux0 s2))
                           ))
;;Functional representation of the loop body.
(define (__loop_body__ s start end)
  (Loop start end 10 s
        (lambda (__s i)
          (let ([mts___0 ($-mts___0 __s)]
                [aux0 ($-aux0 __s)])
              ($ (max 0 (+ mts___0 (vector-ref a i))) (+ aux0 (vector-ref a i)))))))

(define (__join__ $L $R)
  (let
      ([mts___0-$L ($-mts___0 $L)] [aux0-$L ($-aux0 $L)]
       [mts___0-$R ($-mts___0 $R)] [aux0-$R ($-aux0 $R)])
    (let ([aux0
           (+ (bExpr:num->num mts___0-$L aux0-$L mts___0-$R aux0-$R 1)
              (bExpr:num->num mts___0-$L aux0-$L mts___0-$R aux0-$R 1))])
      ($ (max (bExpr:num->num mts___0-$L aux0-$L mts___0-$R aux0-$R 1)
              (bExpr:num->num mts___0-$L aux0-$L mts___0-$R aux0-$R 1)) aux0)))
  )

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic aux00 integer?)
(define $initial ($ 0 (choose 0 1 #t #f)))
;;Actual synthesis work happens here

(define odot
  (synthesize
   #:forall (list i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
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
