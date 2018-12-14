#lang rosette

(require rosette/lib/synthax
         synthools/lib)
;; TIME = 14/10/118 - 15:24:41

(current-bitwidth #f)

(struct $ii (mbs lsum) #:transparent)
(define ($ii-eq? s1 s2) (and (eq? ($ii-mbs s1) ($ii-mbs s2)) (eq? ($ii-lsum s1) ($ii-lsum s2))))



(define-symbolic A$0 A$1 A$2 A$3 A$4 A$5 A$6 A$7 A$8 A$9 integer?)
(define A (list A$0 A$1 A$2 A$3 A$4 A$5 A$6 A$7 A$8 A$9))




;;Functional representation of the loop body.
(define (__loop_body__ s i_begin_0 i_end_1 )
  (Loop i_begin_0 i_end_1 10 s
        (lambda (__s8 i)
          (let
              ([mbs ($ii-mbs __s8)]
               [lsum ($ii-lsum __s8)])
            (let ([lsum (list-ref A i)])
              (let ([mbs (max (+ mbs lsum) 0)])
                ($ii mbs lsum)))))))

;;Wrapping for the sketch of the join.


;;-------------------------------
(define (__join__ left_state9 right_state10)
  (let ([l.mbs ($ii-mbs left_state9)]
        [l.lsum ($ii-lsum left_state9)]
        [r.mbs ($ii-mbs right_state10)]
        [r.lsum ($ii-lsum right_state10)])
    (let ([mbs (max
                ;; (+
                ;;  (NumExprBasic l.lsum r.lsum l.mbs r.mbs 1)
                ;;  (NumExprBasic l.lsum r.lsum l.mbs r.mbs 1))
                ;; (NumExprBasic r.lsum r.mbs 1))
                (+ l.mbs r.lsum)
                r.mbs
                0
                )
               ])
      ($ii mbs r.lsum))))


;;Symbolic input state and synthesized id state
(define $_identity ($ii 0 0 ))
(define $_initial ($ii 0 0))
;;Actual synthesis work happens here

(define odot (synthesize
              #:forall (list A$0 A$1 A$2 A$3 A$4 A$5 A$6 A$7 A$8 A$9)
              #:guarantee (assert (and
                                   ;; ($ii-eq? (__loop_body__ $_initial 0 2 )
                                   ;;          (__join__ (__loop_body__ ($_initial 0 1) 0 1 )
                                   ;;                    (__loop_body__ ($_initial 1 2) 1 2 )))
                                   ;; ($ii-eq? (__loop_body__ ($_initial 0 7) 0 7 )
                                   ;;          (__join__ (__loop_body__ $_initial 0 1 )
                                   ;;                    (__loop_body__ $_initial 1 7 ) 0 7))
                                   ($ii-eq? (__loop_body__ $_initial 0 5 )
                                            (__join__ (__loop_body__ $_initial 0 2 )
                                                      (__loop_body__ $_initial 2 5 )))
                                   ($ii-eq? (__loop_body__ ($_initial 0 8) 0 8 )
                                            (__join__ (__loop_body__ $_initial 0 5 )
                                                      (__loop_body__ $_initial 5 8 )))
                                   ;; ($ii-eq? (__loop_body__ ($_initial 0 9) 0 9 )
                                   ;;          (__join__ (__loop_body__ ($_initial 0 3) 0 3 ) (__loop_body__ ($_initial 3 9) 3 9 ) 0 9))
                                   ;; ($ii-eq? (__loop_body__ ($_initial 0 3) 0 3 )
                                   ;;          (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 3) 2 3 ) 0 3))
                                   ;; ($ii-eq? (__loop_body__ ($_initial 0 4) 0 4 )
                                   ;;          (__join__ (__loop_body__ ($_initial 0 2) 0 2 ) (__loop_body__ ($_initial 2 4) 2 4 ) 0 4))
                                   ))))


(if (sat? odot) (print-forms odot) (print "UNSAT"))
