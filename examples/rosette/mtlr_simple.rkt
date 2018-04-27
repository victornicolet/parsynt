;; This is a test sketch for maximum top-left square example
#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)


(define i0 0)
(define iN 5)
(define (list-set! l i v)
  (list-set l i v))

;; (define ai (list 1 3 5 -10 4 4 1 1 1 1 1))
;; (define a (list ai))


(define-symbolic a$0 a$1 a$2 a$3 a$4 a$5 integer?)
(define ai (list a$0 a$1 a$2 a$3 a$4 a$5))
(define a (list ai))

(define-symbolic j integer?)

(struct $ (c mtr sum))
(define ($-eq? s1 s2) (and (eq? ($-c s1) ($-c s2))
                           (eq? ($-mtr s1) ($-mtr s2))  (eq? ($-sum s1) ($-sum s2))))

;;Functional representation of the loop body.
(define (__loop_body__ s)
  (let
      ([state
        (Loop i0 iN 10 s
              (lambda (__s j) (let ([c ($-c __s)] [mtr ($-mtr __s)] [sum ($-sum __s)])
                                (let ([cl
                                       (list-set c j (+ (list-ref c j)
                                                        (+ sum (list-ref (list-ref a 0) j))))])
                                  ($ cl (max (list-ref cl j) mtr)
                                     (+ sum (list-ref (list-ref a 0) j)))))))])
    ($ ($-c state) ($-mtr state) 0)))

;;Wrapping for the sketch of the join.
(define (__join__ $L $R)
  (let ([l.c ($-c $L)]
        [l.mtr ($-mtr $L)]
        [l.sum ($-sum $L)]
        [x.c ($-c $R)]
        [x.mtr ($-mtr $R)]
        [x.sum ($-sum $R)])
    (let ([state
           (Loop i0 iN 10 ($ l.c 0 0)
                 (lambda (__s j)
                   (let (
                         [c ($-c __s)]
                         [mtr ($-mtr __s)]
                         [sum ($-sum __s)]
                         )
                     (let
                         ;; Here when the expression can use sum the expression goes wrong...?
                         ([cl (list-set c j (NumExprBasic (list-ref c (choose j (sub1 j) (add1 j)))
                                                          (list-ref x.c (choose j (sub1 j) (add1 j)))
                                                          1))]) ;; ---> WORKS OK with SIZE=4,5
                         ;; Here when the expression can use sum the expression goes wrong...?
                         ;; ([cl (list-set c j (NumExprBasic sum (list-ref c j)
                         ;;                                  (list-ref x.c j)
                         ;;                                  1))]) ;; ---> WORKS OK SIZE=4,5
                         ($ cl
                            (NumExprBasic mtr (list-ref cl j) 1)
                            0)))))])
      state)))


;;Symbolic input state and synthesized id state
(define $_identity ($ (let ([c (choose 0 1 #t #f)]) (list c c c c c))
                              (choose 0 1 #t #f 0)
                              (choose 0 1 #t #f 0)))
;; (define $_identity ($ (list 0 0 0 0 0) 0 0))
(define-symbolic x$0 x$1 x$2 x$3 x$4 x$5 integer?)
(define $_initial ($ (list x$0 x$1 x$2 x$3 x$4 x$5) 0 0))
;;Actual synthesis work happens here

 (define odot (time (synthesize
  #:forall (list x$0 x$1 x$2 x$3 x$4 a$0 a$1 a$2 a$3 a$4)
  #:guarantee (assert ($-eq? (__join__ $_initial (__loop_body__ $_identity))
                             (__loop_body__ $_initial))))))

(print-forms odot)
