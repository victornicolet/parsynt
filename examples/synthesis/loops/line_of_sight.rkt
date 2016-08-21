#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (amax visible))
(define ($-eq? s1 s2) (and (eq? ($-amax s1) ($-amax s2))
                           (eq? ($-visible s1) ($-visible s2))
                           ))
;;Functional representation of the loop body.
(define (__loop_body__ s start end)
  (Loop start end 10 s
        (lambda (__s i)
          (let ([amax ($-amax __s)]
                [visible ($-visible __s)]) ($ (max  amax  (vector-ref a i))
                                              (<=  amax  (vector-ref a i)))))))
(define (__join__ $L $R)
  (let
      ([amax-$L ($-amax $L)] [visible-$L ($-visible $L)] [amax-$R ($-amax $R)]
       [visible-$R ($-visible $R)])
    ($
     (max amax-$L amax-$R)
     (<= amax-$L amax-$R)
  )))
 ;; ($ (max  (bExpr:num->num amax-$L visible-$L amax-$R visible-$R 1)
 ;;             (bExpr:num->num amax-$L visible-$L amax-$R visible-$R 1))
 ;;       (<=  (bExpr:num->num amax-$L visible-$L amax-$R visible-$R 1)
 ;;            (bExpr:num->num amax-$L visible-$L amax-$R visible-$R 1))))

;;Symbolic input state and synthesized id state
(define __$0__ ($ (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define $initial ($ 0 #t))

;;Actual synthesis work happens here
(define odot
  (synthesize
   #:forall (list i a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
   #:guarantee (assert
                (and
                 ($-eq?
                  (__loop_body__ $initial 0 0)
                  (__join__  (__loop_body__ $initial 0 0)  (__loop_body__ __$0__ 0 0)))

                 ($-eq?
                  (__loop_body__ $initial 0 9)
                  (__join__  (__loop_body__ $initial 0 0)  (__loop_body__ __$0__ 0 9)))

                 ($-eq?
                  (__loop_body__ $initial 0 9)
                  (__join__  (__loop_body__ $initial 0 9)  (__loop_body__ __$0__ 9 9)))

                 ($-eq?
                  (__loop_body__ $initial 0 9)
                  (__join__  (__loop_body__ $initial 0 4)  (__loop_body__ __$0__ 4 9)))

                 ($-eq?
                  (__loop_body__ $initial 0 9)
                  (__join__  (__loop_body__ $initial 0 5)  (__loop_body__ __$0__ 5 9)))

                 ($-eq?
                  (__loop_body__ $initial 3 9)
                  (__join__  (__loop_body__ $initial 3 6)  (__loop_body__ __$0__ 6 9)))

                 ($-eq?
                  (__loop_body__ $initial 9 9)
                  (__join__  (__loop_body__ $initial 9 9)  (__loop_body__ __$0__ 9 9)))
                 ))))

(define output-file
  (open-output-file "/tmp/conSynthSoldee524.rkt" #:exists 'truncate))
