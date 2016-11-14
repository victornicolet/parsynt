#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic str$1 str$2 str$3 str$4 str$5 str$6 str$7 str$8 str$9 str$10 integer?)
(define str (vector str$1 str$2 str$3 str$4 str$5 str$6 str$7 str$8 str$9 str$10))
(define-symbolic i integer?)

(struct $ (res ten))
(define ($-eq? s1 s2) (and
                       (eq? ($-res s1) ($-res s2))
                       (eq? ($-ten s1) ($-ten s2))))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
 (lambda (__s i)
   (let ([res ($-res __s)][ten ($-ten __s)])
     ($ (+ (* res 10) (vector-ref str i)) (* ten 10))))))

(define (__join__ $L $R)
(let
    ([res-$L ($-res $L)] [res-$R ($-res $R)]
     [ten-$L ($-ten $L)] [ten-$R ($-ten $R)])
  ($ (+ (* (choose res-$L res-$R ten-$L ten-$R 1)
           (choose res-$L res-$R ten-$L ten-$R 1))
        (bExpr:num->num res-$L res-$R ten-$L ten-$R 1))
     (* (choose res-$L res-$R ten-$L ten-$R 1)
        (choose res-$L res-$R ten-$L ten-$R 1)))))

;;Symbolic input state and synthesized id state
(define $_ident ($ (choose 0 1 #t #f) (choose 0 1)))
(define $_init ($ 0 1))
;;Actual synthesis work happens here

(define odot
  (time
   (synthesize
    #:forall (list i    str$1 str$2 str$3 str$4 str$5 str$6 str$7 str$8 str$9 str$10)
    #:guarantee (assert
                 (and
                  ($-eq?
                   (__loop_body__ $_init 0 4)
                   (__join__  (__loop_body__ $_init 0 2)  (__loop_body__ $_init 2 4)))

                  ($-eq?
                   (__loop_body__ $_init 0 4)
                   (__join__  (__loop_body__ $_init 0 1)  (__loop_body__ $_init 1 4)))

                  ($-eq?
                   (__loop_body__ $_init 0 5)
                   (__join__  (__loop_body__ $_init 0 3)  (__loop_body__ $_init 3 5)))

                  ;; ($-eq?
                  ;;  (__loop_body__ $_init 0 9)
                  ;;  (__join__  (__loop_body__ $_init 0 4)  (__loop_body__ $_init 4 9)))

                  ;; ($-eq?
                  ;;  (__loop_body__ $_init 0 7)
                  ;;  (__join__  (__loop_body__ $_init 0 5)  (__loop_body__ $_init 5 7)))

                  ;; ($-eq?
                  ;;  (__loop_body__ $_init 3 9)
                  ;;  (__join__  (__loop_body__ $_init 3 6)  (__loop_body__ $_init 6 9)))

                  ;; ($-eq?
                  ;;  (__loop_body__ $_init 2 9)
                  ;;  (__join__  (__loop_body__ $_init 2 7)  (__loop_body__ $_init 7 9)))
                  ))
                  ))
    )

(print-forms odot)
