#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic coeffs$1 coeffs$2 coeffs$3 coeffs$4 coeffs$5 coeffs$6 coeffs$7 coeffs$8 coeffs$9 coeffs$10 integer?)
(define coeffs (vector coeffs$1 coeffs$2 coeffs$3 coeffs$4 coeffs$5 coeffs$6 coeffs$7 coeffs$8 coeffs$9 coeffs$10))
(define-symbolic i x integer?)

(struct $ (res factor))
(define ($-eq? s1 s2) (and (eq? ($-res s1) ($-res s2))
 (eq? ($-factor s1) ($-factor s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
 (lambda (__s i)
(let ([res ($-res __s)]
  [factor ($-factor __s)]) ($ (+ res (* factor (vector-ref coeffs i)))
                           (* x factor))))))
(define (__join__ $L $R)
(let
 ([res-$L ($-res $L)] [factor-$L ($-factor $L)] [res-$R ($-res $R)]
  [factor-$R ($-factor $R)])
 ($ (+ (* (choose res-$L factor-$L res-$R factor-$R )
          (choose res-$L factor-$L res-$R factor-$R ))
       (choose  res-$L factor-$L res-$R factor-$R))
    (* (choose  res-$L factor-$L res-$R factor-$R )
       (choose  res-$L factor-$L res-$R factor-$R )))))


;;Symbolic input state and synthesized id state
(define $_ident ($ (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define $_init ($ 0 1))
;;Actual synthesis work happens here

(define odot
  (time
   (synthesize
    #:forall (list i x coeffs$1 coeffs$2 coeffs$3 coeffs$4 coeffs$5 coeffs$6 coeffs$7 coeffs$8 coeffs$9 coeffs$10)
    #:guarantee (assert
                 (and
                  ($-eq?
                   (__loop_body__ $_init 0 4)
                   (__join__  (__loop_body__ $_init 0 2)  (__loop_body__ $_init 2 4)))

                  ($-eq?
                   (__loop_body__ $_init 0 5)
                   (__join__  (__loop_body__ $_init 0 3)  (__loop_body__ $_init 3 5)))

                  ($-eq?
                   (__loop_body__ $_init 0 5)
                   (__join__  (__loop_body__ $_init 0 2)  (__loop_body__ $_init 2 5)))

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
    )))

(print-forms odot)
