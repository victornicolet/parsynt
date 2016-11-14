#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (lev_dist last))
(define ($-eq? s1 s2) (and (eq? ($-lev_dist s1) ($-lev_dist s2))
                           (eq? ($-last s1) ($-last s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
  (Loop _iL_ _iR_ 10 s
        (lambda (__s i)
          (let
              ([lev_dist ($-lev_dist __s)][last ($-last __s)])
            ($ (+ lev_dist (if (= (modulo i 2) 0)
                               (vector-ref a i) (- (vector-ref a i))))
               (modulo _iR_ 2))))))

(define (__join__ $L $R)
(let
    ([lev_dist-$L ($-lev_dist $L)] [lev_dist-$R ($-lev_dist $R)]
     [last-$L ($-last $L)] [last-$R ($-last $R)])
  ($ (+ (bExpr:num->num  lev_dist-$L lev_dist-$R 1)
        (if (= (bExpr:num->num last-$L last-$R lev_dist-$L lev_dist-$R 1)
               (bExpr:num->num  lev_dist-$L lev_dist-$R last-$L last-$R 1))
            (bExpr:num->num  lev_dist-$L lev_dist-$R 1)
            (bExpr:num->num  lev_dist-$L lev_dist-$R 1)))
            (bExpr:num->num  lev_dist-$L lev_dist-$R last-$L last-$R 1))))


;;Symbolic input state and synthesized id state
(define $_ident ($ (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define $_init ($ 0 0))
;;Actual synthesis work happens here

(define odot
  (time
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

                  )
                 ))))

(print-forms odot)
