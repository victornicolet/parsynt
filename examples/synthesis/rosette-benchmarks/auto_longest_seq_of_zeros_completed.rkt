#lang rosette

(require rosette/lib/synthax
         consynth/lib)

(current-bitwidth #f)
(define-symbolic a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10 boolean?)
(define a (vector a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10))
(define-symbolic i integer?)

(struct $ (cl ml c conj))
(define ($-eq? s1 s2) (and (eq? ($-cl s1) ($-cl s2))
 (eq? ($-ml s1) ($-ml s2))  (eq? ($-c s1) ($-c s2))
 (eq? ($-conj s1) ($-conj s2))
))
;;Functional representation of the loop body.
(define (__loop_body__ s _iL_ _iR_)
 (Loop _iL_ _iR_ 10 s
 (lambda (__s i)
(let ([cl ($-cl __s)] [ml ($-ml __s)] [c ($-c __s)]
      [conj ($-conj __s)])
  ($ (if (vector-ref a i) (+ cl 1) 0)
     (max ml (if (vector-ref a i) (+ cl 1) 0))
     (+ c (if conj 1 0))
     (and conj (vector-ref a i)))))))


(define (__join__ $L $R)
(let
 ([cl-$L ($-cl $L)] [ml-$L ($-ml $L)] [c-$L ($-c $L)] [conj-$L ($-conj $L)]
  [cl-$R ($-cl $R)] [ml-$R ($-ml $R)] [c-$R ($-c $R)] [conj-$R ($-conj $R)])
 ($ (if (bExpr:boolean  conj-$L conj-$R 1) ;; should be conj-r
        (bExpr:num->num  cl-$L ml-$L c-$L cl-$R ml-$R c-$R 1) ;; should be cl-r + cl-l
        (bExpr:num->num  cl-$L ml-$L c-$L cl-$R ml-$R c-$R 1)) ;; should be cl-r

    (max (bExpr:num->num  cl-$L ml-$L c-$L cl-$R ml-$R c-$R 1) ;; max (m-l m-r)
         (bExpr:num->num  cl-$L ml-$L c-$L cl-$R ml-$R c-$R 1)) ;; cl-l + c-r

    (+ (bExpr:num->num  cl-$L ml-$L c-$L cl-$R ml-$R c-$R 1) ;; c-r
       (if (bExpr:boolean  conj-$L conj-$R 1) ;; conj-r
           (bExpr:num->num  cl-$L ml-$L c-$L cl-$R ml-$R c-$R 1) ;; c-r + c-l
           (bExpr:num->num  cl-$L ml-$L c-$L cl-$R ml-$R c-$R 1))) ;; c-r

    (and (bExpr:boolean  conj-$L conj-$R 1) (bExpr:boolean  conj-$L conj-$R 1)))) ;; conj-r && conj-l
)

;;Symbolic input state and synthesized id state
(define $_init ($ (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f) (choose 0 1 #t #f)))
(define $initial ($ 0 0 0 true))
;;Actual synthesis work happens here

(define odot
(synthesize
#:forall (list i    a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 a$10)
#:guarantee (assert
(and
 ($-eq?
 (__loop_body__ $initial 0 4)
(__join__  (__loop_body__ $initial 0 2)  (__loop_body__ $_init 2 4)))

($-eq?
 (__loop_body__ $initial 0 9)
(__join__  (__loop_body__ $initial 0 3)  (__loop_body__ $_init 3 9)))

($-eq?
 (__loop_body__ $initial 0 9)
(__join__  (__loop_body__ $initial 0 7)  (__loop_body__ $_init 7 9)))

($-eq?
 (__loop_body__ $initial 0 9)
(__join__  (__loop_body__ $initial 0 4)  (__loop_body__ $_init 4 9)))

($-eq?
 (__loop_body__ $initial 0 7)
(__join__  (__loop_body__ $initial 0 5)  (__loop_body__ $_init 5 7)))

($-eq?
 (__loop_body__ $initial 3 9)
(__join__  (__loop_body__ $initial 3 6)  (__loop_body__ $_init 6 9)))

($-eq?
 (__loop_body__ $initial 2 9)
(__join__  (__loop_body__ $initial 2 7)  (__loop_body__ $_init 7 9)))
))
))
