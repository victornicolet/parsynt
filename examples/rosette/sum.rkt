#lang rosette

(require rosette/lib/synthax
         synthools/lib)

(current-bitwidth #f)

(define-symbolic a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9 integer?)
(define a (list a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9))

;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_ i_end_ )
  ;; Loop is a macro that simply calls the function argument recursively,
  ;; here (i_end - i_begin) times.
  (Loop i_begin_ i_end_ 10 s
    (lambda (sum i) (+ sum (list-ref a i)))))

;;Wrapping for the sketch of the join.
(define (__join__ lsum rsum)
  ((choose + -) ((choose + * -) (choose lsum rsum 1 0)
                 (choose lsum rsum 1 0))
        ((choose + * -)  (choose lsum 1 0)
                       (choose lsum 1 0))))

;;Symbolic input state and synthesized id state
(define $_identity (choose 0 1 #t #f 0))
(define-symbolic sum0 integer?)
(define $_initial sum0)
;;Actual synthesis work happens here

(define odot
  (time
   (synthesize
;;    #:forall (list a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9) ;; real time 3.321
    #:forall (list sum0 a$0 a$1 a$2 a$3 a$4 a$5 a$6 a$7 a$8 a$9) ;; real time 3.299
    #:guarantee (assert (and
                         (= (__loop_body__ $_initial 0 2 )
                                (__join__ (__loop_body__ $_initial 0 1 ) (__loop_body__ $_identity 1 2 )))
                         (= (__loop_body__ $_initial 0 7 )
                                (__join__ (__loop_body__ $_initial 0 1 ) (__loop_body__ $_identity 1 7 )))
                         (= (__loop_body__ $_initial 0 5 )
                                (__join__ (__loop_body__ $_initial 0 2 ) (__loop_body__ $_identity 2 5 )))
                         (= (__loop_body__ $_initial 0 8 )
                                (__join__ (__loop_body__ $_initial 0 5 ) (__loop_body__ $_identity 5 8 )))
                         (= (__loop_body__ $_initial 0 9 )
                                (__join__ (__loop_body__ $_initial 0 3 ) (__loop_body__ $_identity 3 9 )))
                         (= (__loop_body__ $_initial 0 3 )
                                (__join__ (__loop_body__ $_initial 0 2 ) (__loop_body__ $_identity 2 3 )))
                         (= (__loop_body__ $_initial 0 4 )
                                (__join__ (__loop_body__ $_initial 0 2 ) (__loop_body__ $_identity 2 4 ))))))))

(print-forms odot)
