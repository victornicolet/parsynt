#lang rosette

(require consynth/lib/synthax/constructors
         consynth/lib/synthax/expressions
         rosette/lib/synthax
         "../utils.rkt")

(define limit 10)

(define-struct state (sum start end))

(define (state-eq a b) (= (state-sum a) (state-sum b)))

(define (body l s_)
  (let
      ([sum (state-sum s_)]
       [start (state-start s_)]
       [end (state-end s_)])
  (Loop start end limit s_
        (lambda (s i)
          (let
              ([sum_ (state-sum s)]
               [start_ (state-start s)]
               [end_ (state-end s)])
            (state (+ sum_ (vector-ref l i)) start_ end_))))))

(define (init-state start end) (state (??) start end))

(define (join L R)
  (let
      ([sum-left (state-sum L)]
       [sum-right (state-sum R)]
       [start-left (state-start L)]
       [end-left (state-end L)]
       [start-right (state-start R)]
       [end-right (state-end R)])
    (state (bExpr:int->int sum-left sum-right 1) start-left end-right)))

;; ****************************************************************
;; Benchmark 1 wth h(x++y) = h(x) # h(y) vcs

(define-syntax-rule (problem v st m end s0)
  (state-eq (body v (state s0 st end))
            (join (body v (state s0 st m)) (body v (init-state m end)))))

(define (solve-func-pb)
  (define-symbolic i0 i1 i2 i3 i4 i5 i6 i7 i8 s integer?)
  ;; Join point (symbolic)

  (define symbv
    (list->vector (list i0 i1 i2 i3 i4 i5 i6 i7 i8)))
  (sat? (synthesize
   #:forall (list i0 i1 i2 i3 i4 i5 i6 i7 i8 s)
   #:guarantee (assert (and
                        (problem symbv 0 0 8 s)
                        (problem symbv 0 4 7 s)
                        (problem symbv 0 5 7 s)
                        (problem symbv 0 6 6 s)
                        (problem symbv 6 6 6 s)
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

(define-syntax-rule (problem2 v a b st m end)
   (and
    (state-eq (join (state a m m) (body v (state b m end)))
              (body v (join (state a m m) (state b m end))))
    (state-eq (join (state a st m) (init-state m end)) (state a st m))))


(define (solve-imper-pb)
  (define-symbolic i0 i1 i2 i3 i4 i5 i6 i7 i8 a b integer?)
  ;; Join point (symbolic)

  (define symbv
    (list->vector (list i0 i1 i2 i3 i4 i5 i6 i7 i8)))


   (synthesize
    #:forall (list i0 i1 i2 i3 i4 i5 i6 i7 i8 a b)
    #:guarantee (assert (and
                        (problem2 symbv a b 0 3 7)
                        (problem2 symbv a b 1 3 3)
                        (problem2 symbv a b 0 4 5)
                        (problem2 symbv a b 5 6 7)
                        (problem2 symbv a b 3 8 8)
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

(benchmark2)
