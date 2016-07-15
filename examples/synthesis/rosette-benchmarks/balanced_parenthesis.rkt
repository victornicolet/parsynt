#lang rosette

(require consynth/lib/synthax/constructors
         consynth/lib/synthax/expressions
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
             start end))))))

(define (init-state start end) (state (choose true false) (??) (??) start end))

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
     (& l_wb (bExpr:int->bool l_diff r_diff l_h r_h))
     (bExpr:int->int l_h r_h l_diff r_diff 1)
     (min (bExpr:int->int l_h r_h l_diff r_diff 1)
          (bExpr:int->int l_h r_h l_diff r_diff 1))
     start-left
     end-right)))

;; ****************************************************************
;; Benchmark 1 wth h(x++y) = h(x) # h(y) vcs

(define-syntax-rule (problem v st m end wb0 diff0 hmin0)
  (state-eq (body v (state wb0 diff0 hmin0 st end))
            (join (body v (state wb0 diff0 hmin0 st m))
                  (body v (init-state m end)))))

(define (solve-func-pb)
  (define-symbolic i0 i1 i2 i3 i4 i5 i6 i7 i8 diff hm integer?)
  (define-symbolic wb boolean?)
  ;; Join point (symbolic)

  (define symbv
    (list->vector (list i0 i1 i2 i3 i4 i5 i6 i7 i8)))
  (sat? (synthesize
   #:forall (list i0 i1 i2 i3 i4 i5 i6 i7 i8 diff hm)
   #:guarantee (assert (and
                        (problem symbv 0 0 8 wb diff hm)
                        (problem symbv 0 4 7 wb diff hm)
                        (problem symbv 0 5 7 wb diff hm)
                        (problem symbv 0 6 6 wb diff hm)
                        (problem symbv 6 6 6 wb diff hm)
                        )))))
(define (test-unit)
  (define-values (modl cpu real gbc)
    (time-apply solve-func-pb '()))
  (if modl (integer->real cpu) -inf.0))

(define (benchmark1)
  (define tests (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17))
  (exact->inexact
   (/ (foldl
       (λ (s i) (+ s
                   (test-unit)))
       0
       tests)
      (integer->real(length tests)))))

(benchmark1)

;; ****************************************************************
;; Benchmark 2 : vcs s # B(s,i) = B(s # s, i)

(define-syntax-rule (problem2 v wb0 diff0 hmin0 wb1 diff1 hmin1 st m end)
   (and
    (state-eq (join (state wb0 diff0 hmin0 m m)
                    (body v (state wb1 diff1 hmin1 m end)))
              (body v (join (state wb0 diff0 hmin0 m m)
                            (state wb1 diff1 hmin1 m end))))

    (state-eq (join (state wb0 diff0 hmin0 st m) (init-state m end))
              (state wb0 diff0 hmin0 st m))))


(define (solve-imper-pb)
  (define-symbolic i0 i1 i2 i3 i4 i5 i6 i7 i8 di di0 hm hm0 integer?)
  (define-symbolic wb wb0 boolean?)
  ;; Join point (symbolic)

  (define symbv
    (list->vector (list i0 i1 i2 i3 i4 i5 i6 i7 i8)))


   (synthesize
    #:forall (list i0 i1 i2 i3 i4 i5 i6 i7 i8 di di0 hm hm0 wb wb0)
    #:guarantee (assert (and
                        (problem2 symbv wb di hm wb0 di0 hm0 0 3 7)
                        (problem2 symbv wb di hm wb0 di0 hm0 1 3 3)
                        (problem2 symbv wb di hm wb0 di0 hm0 0 4 5)
                        (problem2 symbv wb di hm wb0 di0 hm0 5 6 7)
                        (problem2 symbv wb di hm wb0 di0 hm0 3 8 8)
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

;(benchmark2)
