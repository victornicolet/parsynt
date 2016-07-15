#lang rosette

(require consynth/lib/synthax/constructors
         consynth/lib/synthax/expressions
         rosette/lib/synthax
         "../utils.rkt")

(define limit 10)
(current-bitwidth #f)

(define-struct state (mps sum start end))

(define (state-eq a b)
  (and (= (state-mps a) (state-mps b))
       (= (state-sum a) (state-sum b))))

(define (body v s_)
  (let
      ([start (state-start s_)]
       [end (state-end s_)])
    (Loop start end limit s_
          (lambda (s i)
            (let* ([start (state-start s)]
                   [end (state-end s)]
                   [mps (state-mps s)]
                   [sum (state-sum s)]
                   [a (vector-ref v i)])
              (state
               (max mps (+ sum a))
               (+ sum a)
               start
               end))))))

(define (init-state start end) (state (??) (??) start end))

(define (join L R)
  (let
      ([start-left (state-start L)]
       [end-left (state-end L)]
       [start-right (state-start R)]
       [end-right (state-end R)]
       [sum-left (state-sum L)]
       [sum-right (state-sum R)]
       [mps-left (state-mps L)]
       [mps-right (state-mps R)])
    (state
     (state-mps
      (body (vector (bExpr:int->int sum-left sum-right mps-left mps-right 1)
                  (bExpr:int->int sum-left sum-right mps-left mps-right 1)
                  (bExpr:int->int sum-left sum-right mps-left mps-right 1)
                  (bExpr:int->int sum-left sum-right mps-left mps-right 1))
            (init-state 0 4)))

     (bExpr:int->int sum-left sum-right mps-left mps-right 1)

     start-left
     end-right)))


;; ****************************************************************
;; Benchmark 1 wth h(x++y) = h(x) # h(y) vcs

(define-syntax-rule (problem v st m end)
  (let ([sum 0][mps 0])
    (state-eq (body v (state mps sum  st end))
              (join (body v (state mps sum st m))
                    (body v (init-state m end))))))

(define-symbolic b0 b1 b2 b3 b4 b5 b6 b7 b8 integer?)
(define symbv
  (vector b0 b1 b2 b3 b4 b5 b6 b7 b8))

(verify (assert (problem symbv 0 2 9)))

(define (solve-func-pb)

  (define-symbolic b0 b1 b2 b3 b4 b5 b6 b7 b8 integer?)
  (define symbv
    (vector b0 b1 b2 b3 b4 b5 b6 b7 b8))

  (sat?
   (synthesize
    #:forall (list b0 b1 b2 b3 b4 b5 b6 b7 b8)
    #:guarantee (assert (and
                         (problem symbv 0 0 8)
                         (problem symbv 0 4 7)
                         (problem symbv 0 5 8)
                         (problem symbv 6 6 6))))))

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

(if (solve-func-pb)
    (displayln "Benchmark / functional")
    (displayln "Bench1 failed."))

(benchmark1)

;; ****************************************************************
;; Benchmark 2 : vcs s # B(s,i) = B(s # s, i)

(define-syntax-rule (problem2 v st m end)
  (let ([mps 0][sum 0])
    (and
     (state-eq (join (state mps sum m m)
                     (body v (state mps sum m end)))
               (body v (join (state mps sum m m)
                             (state mps sum m end))))

     (state-eq (join (state mps sum st m) (init-state m end))
               (state mps sum st m)))))


(define (solve-imper-pb)
  (define-symbolic  i0 i1 i2 i3 i4 i5 i6 i7 i8 integer?)
  ;; Join point (symbolic)

  (define symbv
    (list->vector (list  i0 i1 i2 i3 i4 i5 i6 i7 i8)))

   (sat?
    (synthesize
     #:forall (list  i0 i1 i2 i3 i4 i5 i6 i7 i8)
     #:guarantee (assert
                  (and
                   (problem symbv 0 0 8)
                   (problem symbv 0 4 7)
                   (problem symbv 0 5 8)
                   (problem symbv 0 3 6)
                   (problem symbv 6 6 6)
                  )))))


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


(if (solve-imper-pb)
    (displayln "Benchmark / imperative")
    (displayln "Bench2 failed."))

(benchmark2)
