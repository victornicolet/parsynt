#lang rosette

(require rosette/lib/synthax
         consynth/lib
         "../utils.rkt")


(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (wb diff hmin))
(define ($-eq? s1 s2) (and (eq? ($-wb s1) ($-wb s2))
                           (eq? ($-diff s1) ($-diff s2))
                           (eq? ($-hmin s1) ($-hmin s2))))


;;Functional representation of the loop body.
(define (__loop_body__ s start end)
 (Loop start end 10 s
 (lambda (__s i)
   (let
       ([wb ($-wb __s)][diff ($-diff __s)][hmin ($-hmin __s)])
     (let
         ([diff (if (vector-ref a i) (add1 diff) (sub1 diff))])
       ($  (and (not (< diff 0)) wb)
           diff
           (min diff hmin)))))))


(define (__join__ $L $R)
  (let
      ([hmin-$L ($-hmin $L)] [hmin-$R ($-hmin $R)]
       [wb-$L ($-wb $L)] [wb-$R ($-wb $R)]
       [diff-$L ($-diff $L)] [diff-$R ($-diff $R)])
    ($
     (and wb-$L (bExpr:num->bool diff-$L diff-$R hmin-$L hmin-$R 1))
     (bExpr:num->num hmin-$L hmin-$R diff-$L diff-$R 1)
     (min (bExpr:num->num hmin-$L hmin-$R diff-$L diff-$R 1)
          (bExpr:num->num hmin-$L hmin-$R diff-$L diff-$R 1)))))

;;Symbolic input state and synthesized id state
(define __$0__ ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define $initial ($ #t 0 0))
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
