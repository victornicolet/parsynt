#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 integer?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (pos mts aux_1))
(define ($-eq? s1 s2) (and (eq? ($-pos s1) ($-pos s2))
 (eq? ($-mts s1) ($-mts s2))  (eq? ($-aux_1 s1) ($-aux_1 s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
 (lambda (__s i)
(let ([pos ($-pos __s)] [mts ($-mts __s)] [aux_1 ($-aux_1 __s)]) (let ()
 (let ([aux_1 (+ (vector-ref a i) aux_1)])
   ($ (if (= mts 0) i pos) (max 0 (+ mts (vector-ref a i))) aux_1)))))))

(define (__join__ $L $R)
(let
 ([pos-$L ($-pos $L)] [mts-$L ($-mts $L)] [aux_1-$L ($-aux_1 $L)]
  [pos-$R ($-pos $R)] [mts-$R ($-mts $R)] [aux_1-$R ($-aux_1 $R)])
(let ()
  (let ([aux_1 (+ (bExpr:num->num  pos-$L mts-$L aux_1-$L pos-$R mts-$R aux_1-$R 1)
                  (bExpr:num->num  pos-$L mts-$L aux_1-$L pos-$R mts-$R aux_1-$R 1))])
 ($ (if (bExpr:num->bool  pos-$L mts-$L aux_1-$L   pos-$R mts-$R aux_1-$R 1)
      (bExpr:num->num  pos-$L mts-$L aux_1-$L pos-$R mts-$R aux_1-$R 1)
      (bExpr:num->num  pos-$L mts-$L aux_1-$L pos-$R mts-$R aux_1-$R 1))
    (max (bExpr:num->num  pos-$L mts-$L aux_1-$L pos-$R mts-$R aux_1-$R 1)
         (bExpr:num->num  pos-$L mts-$L aux_1-$L pos-$R mts-$R aux_1-$R 1))
   aux_1)))))

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define-symbolic aux_10 integer?)
(define $initial ($ -1 0 aux_10))
;;Actual synthesis work happens here

(define odot
(synthesize
#:forall (list i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
#:guarantee (assert
(and
 ($-eq?
 (__loop_body__ $initial 0 4)
(__join__  (__loop_body__ $initial 0 2)  (__loop_body__ $_init 2 4)))

;; ($-eq?
;;  (__loop_body__ $initial 0 9)
;; (__join__  (__loop_body__ $initial 0 3)  (__loop_body__ $_init 3 9)))

;; ($-eq?
;;  (__loop_body__ $initial 0 9)
;; (__join__  (__loop_body__ $initial 0 7)  (__loop_body__ $_init 7 9)))

;; ($-eq?
;;  (__loop_body__ $initial 0 9)
;; (__join__  (__loop_body__ $initial 0 4)  (__loop_body__ $_init 4 9)))

;; ($-eq?
;;  (__loop_body__ $initial 0 7)
;; (__join__  (__loop_body__ $initial 0 5)  (__loop_body__ $_init 5 7)))

;; ($-eq?
;;  (__loop_body__ $initial 3 9)
;; (__join__  (__loop_body__ $initial 3 6)  (__loop_body__ $_init 6 9)))

;; ($-eq?
;;  (__loop_body__ $initial 2 9)
;; (__join__  (__loop_body__ $initial 2 7)  (__loop_body__ $_init 7 9)))
))
))
