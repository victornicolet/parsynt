#lang rosette

(require rosette/lib/synthax
         consynth/lib
         "../utils.rkt")


(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (cnt m first-elm))
(define ($-eq? s1 s2) (and ;;(eq? ($-m s1) ($-m s2))
                           (eq? ($-cnt s1) ($-cnt s2))))
                          ;; (eq? ($-first-elm s1) ($-first-elm s2))))


;;Functional representation of the loop body.
(define (__loop_body__ s start end)
  (Loop start end 10 s
        (lambda (__s i)
          (let
              ([m ($-m __s)][cnt ($-cnt __s)][first-elm ($-first-elm __s)])
            ($
             (if (and (vector-ref a i) (not m)) (add1 cnt) cnt)
             (vector-ref a i)
             (vector-ref a start))))))


(define (__join__ $L $R)
  (let
      ([first-elm-$L ($-first-elm $L)] [first-elm-$R ($-first-elm $R)]
       [m-$L ($-m $L)] [m-$R ($-m $R)]
       [cnt-$L ($-cnt $L)] [cnt-$R ($-cnt $R)])
    ($
     (if (&& (bExpr:bool->bool first-elm-$R m-$R 1)
             (bExpr:bool->bool m-$L first-elm-$L 1))
         (+
          (bExpr:num->num first-elm-$L first-elm-$R cnt-$L cnt-$R m-$L m-$R 1)
          (bExpr:num->num first-elm-$L first-elm-$R cnt-$L cnt-$R m-$L m-$R 1))
         (+
          (bExpr:num->num first-elm-$L first-elm-$R cnt-$L cnt-$R m-$L m-$R 1)
          (bExpr:num->num first-elm-$L first-elm-$R cnt-$L cnt-$R m-$L m-$R 1)))
     (bExpr:bool->bool first-elm-$L m-$L 1)
     first-elm-$L )))

;;Symbolic input state and synthesized id state
(define __$0__ ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define $initial ($ 0 #f #f))
;;Actual synthesis work happens here (sat? odot)

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
                   (__join__  (__loop_body__ $initial 9 9)  (__loop_body__ __$0__ 9 9)))))))

(define (wrap)
        (define output-file
          (open-output-file "/tmp/conSynthSol0b396b.rkt" #:exists 'truncate))
        (if (sat? odot)
            (begin
              (define form_list  (generate-forms odot))
              (map
               (lambda (forms)
                 (displayln (syntax->datum forms) output-file))
               form_list))
            (print "unsat" output-file))
        (close-output-port output-file))

(wrap)
