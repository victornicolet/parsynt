#lang rosette

(require consynth/lib
         rosette/lib/synthax
         "../utils.rkt")

(define limit 10)

(define-struct state (wb diff hmin start end))

(define (state-eq a b)
  (and (eq? (state-wb a) (state-wb b))
       (= (state-diff a) (state-diff b))
       (= (state-hmin a) (state-hmin b))))


(define (& a b) (and a b))
(define (|| a b) (or a b))

(define (body str s_)
  (let
      ([start (state-start s_)]
       [end (state-end s_)])
    (Loop start end limit s_
          (lambda (s i)
            (let* ([start (state-start s)]
                   [end (state-end s)]
                   [wbin (state-wb s)]
                   [diff (state-diff s)]
                   [hmin (state-hmin s)]
                   [diff0 (if (vector-ref str i)
                              (add1 diff)
                              (sub1 diff))])
              (state
               (& (not (< diff0 0)) wbin)
               diff0
               (min diff0 hmin)
               start
               end))))))

(define (init-state start end) (state (choose #t #f) (??) (??) start end))

(define (join L R)
  (let
      (
       [start-left (state-start L)]
       [end-left (state-end L)]
       [start-right (state-start R)]
       [end-right (state-end R)]
       [l_wb (state-wb L)]
       [r_wb (state-wb R)]
       [l_diff (state-diff L)]
       [r_diff (state-diff R)]
       [l_h (state-hmin L)]
       [r_h (state-hmin R)])
    (state
     (& l_wb (bExpr:num->bool l_diff r_diff l_h r_h 1))
     (bExpr:num->num l_h r_h l_diff r_diff 1)
     (min (bExpr:num->num l_h r_h l_diff r_diff 1)
          (bExpr:num->num l_h r_h l_diff r_diff 1))
     start-left
     end-right)))

;; ****************************************************************
;; Benchmark 1 wth h(x++y) = h(x) # h(y) vcs

(define-syntax-rule (problem v st m end)
  (let ([wb0 #t][diff0 0][hmin0 0])
  (state-eq (body v (state wb0 diff0 hmin0 st end))
            (join (body v (state wb0 diff0 hmin0 st m))
                  (body v (init-state m end))))))

(define (solve-func-pb)
  (define-symbolic b0 b1 b2 b3 b4 b5 b6 b7 b8 boolean?)
  ;; Join point (symbolic)

  (define symbv
    (list->vector (list b0 b1 b2 b3 b4 b5 b6 b7 b8)))

  (synthesize
   #:forall (list b0 b1 b2 b3 b4 b5 b6 b7 b8)
   #:guarantee (assert (and
                        (problem symbv 0 0 8)
                        (problem symbv 0 4 7)
                        (problem symbv 0 5 8)
                        (problem symbv 0 6 6)
                        (problem symbv 6 6 6)))))
(define (test-unit)
  (define-values (modl cpu real gbc)
    (time-apply solve-func-pb '()))
  (if modl (integer->real cpu) -inf.0))

(define (benchmark1)
  (define tests (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17))
  (exact->inexact
   (/ (foldl
       (λ (s i) (+ s
                   (test-unit))) 0 tests)
      (integer->real(length tests)))))

(if (sat? (solve-func-pb))
    (displayln "Benchmark / functional")
    (displayln "Bench1 failed."))

;; (benchmark1)

;; ****************************************************************
;; Benchmark 2 : vcs s # B(s,i) = B(s # s, i)

(define-syntax-rule (problem2 v st m end)
  (let ([wb0 #t][diff0 0][hmin0 0])
    (and
     (state-eq (join (state wb0 diff0 hmin0 m m)
                     (body v (state wb0 diff0 hmin0 m end)))
               (body v (join (state wb0 diff0 hmin0 m m)
                             (state wb0 diff0 hmin0 m end))))

     (state-eq (join (state wb0 diff0 hmin0 st m) (init-state m end))
               (state wb0 diff0 hmin0 st m)))))


(define (solve-imper-pb)
  (define-symbolic  b0 b1 b2 b3 b4 b5 b6 b7 b8 boolean?)
  ;; Join point (symbolic)

  (define symbv
    (list->vector (list  b0 b1 b2 b3 b4 b5 b6 b7 b8)))

   (synthesize
    #:forall (list  b0 b1 b2 b3 b4 b5 b6 b7 b8)
    #:guarantee (assert
                 (and
                  (problem symbv 0 0 8)
                  (problem symbv 0 4 7)
                  (problem symbv 0 5 8)
                  (problem symbv 0 6 6)
                  (problem symbv 6 6 6)
                  ))))


(define (test-unit2)
  (define-values (modl cpu real gbc)
    (time-apply solve-imper-pb '()))
  (if modl (integer->real cpu) -inf.0))

(define (benchmark2)
  (define tests (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17))
  (exact->inexact
   (/ (foldl
       (λ (s i) (+ s
                   (test-unit2)))
       0
       tests)
      (integer->real(length tests)))))


(if (sat? (solve-imper-pb))
    (displayln "Benchmark / imperative")
    (displayln "Bench2 failed."))

;;(benchmark2)
