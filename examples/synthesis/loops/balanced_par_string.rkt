#lang rosette

(require rosette/lib/synthax
         consynth/lib/synthax/expressions
         consynth/lib/synthax/constructors)

(current-bitwidth #f)

(define-symbolic a0 a1 a2 a3 a4 a5 a6 a7 boolean?)
(define-symbolic len integer? )
(define split 3)
(assert (< split len))
(assert (< 0 split))
(assert (<= len 8))

(define sym_string
  (list->vector
   (take (list a0 a1 a2 a3 a4 a5 a6 a7) len)))

(define (& a b) (and a b))
(define (|| a b) (or a b))

(struct state (wb diff hmin))
(define (eq-states a b)
  (and (eq? (state-wb a) (state-wb b))
       (= (state-diff a) (state-diff b))
       (= (state-hmin a) (state-hmin b))))

(define (display-state s)
  (display (state-wb s))
  (display "-")
  (display (state-diff s))
  (display "-")
  (displayln (state-hmin s)))

(define (bal-f str start end)
    (Loop start end 8 (state #t 0 0)
          (lambda (s i)
                  (let* ([wbin (state-wb s)]
                         [diff (state-diff s)]
                         [hmin (state-hmin s)]
                         [diff0 (if (vector-ref str i)
                                   (add1 diff)
                                   (sub1 diff))])
                    (state
                     (& (not (< diff0 0)) wbin)
                     diff0
                     (min diff0 hmin))))))

(define (join L R)
  (let ([l_wb (state-wb L)]
        [r_wb (state-wb R)]
        [l_diff (state-diff L)]
        [r_diff (state-diff R)]
        [l_h (state-hmin L)]
        [r_h (state-hmin R)])
    (state
     (& l_wb (bExpr:int->bool l_diff r_diff l_h r_h))
     (bExpr:int->int l_h r_h l_diff r_diff 1)
     (min (bExpr:int->int l_h r_h l_diff r_diff 1)
          (bExpr:int->int l_h r_h l_diff r_diff 1)))))

(define non_sym_string (vector #t #t #f #f #t #t #f #f #t #f))


(define-syntax-rule (synth-case parens from split to)
  (values
   (bal-f parens from split)
   (bal-f parens split to)
   (bal-f parens from to)))

(define (wf-non-sym s len)
  (for ([i (in-range 1 len)])
    (if (eq-states (join (bal-f s 0 i) (bal-f s i len)) (bal-f s 0 len))
        (display i)
        (displayln "Failed"))))

(define-values (ll rr total)
  (synth-case sym_string 0 4 8))
(define join_res (join ll rr))

(define-values (ll0 rr0 total0)
  (synth-case sym_string 0 3 8))
(define join_res0 (join ll0 rr0))

(define-values (ll1 rr1 total1)
  (synth-case sym_string 0 7 8))
(define join_res1 (join ll1 rr1))

(define-values (ll2 rr2 total2)
  (synth-case sym_string 0 5 8))
(define join_res2 (join ll2 rr2))

(if (unsat? (verify  (assert (eq-states total join_res))))
    (displayln "Unsatisfifable verification conditions.")
    (displayln "Verif passed."))

(define odot
  (synthesize
   #:forall (list a0 a1 a2 a3 a4 a5 a6 a7)
   #:guarantee (assert (and
                        (eq-states total2 join_res2)
                        (eq-states total1 join_res1)
                        (eq-states total0 join_res0)
                        (eq-states total join_res)))))


(if (sat? odot) (print-forms odot) (core odot))
