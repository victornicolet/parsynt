#lang rosette

(require rosette/lib/synthax
         consynth/lib/synthax/expressions
         consynth/lib/synthax/constructors)


(define-symbolic a0 a1 a2 a3 a4 a5 a6 a7 boolean?)
(define-symbolic len integer? )
(define split 3)
(assert (< split len))
(assert (< 0 split))
(assert (<= len 8))

(define sym_string
  (list->vector
   (take (list a0 a1 a2 a3 a4 a5 a6 a7) len)))

(struct state (cr c hmin))

(define (bal-f str start end)
    (Loop start end 10 (state #t 0 0)
          (lambda (s i)
                  (let* ([wbin (state-cr s)]
                         [diff (state-c s)]
                         [hmin (state-hmin s)]
                         [diff0 (if (vector-ref str i)
                                   (add1 diff)
                                   (sub1 diff))]
                         [wb (if (> diff0 0) #f #t)]
                         [nhmin (if (<= diff0 hmin)
                                    diff0
                                    hmin)])
                    (state wb diff0 nhmin)))))

(define (join R L)
  (let ([l_cr (state-cr L)]
        [r_cr (state-cr R)]
        [l_c (state-c L)]
        [r_c (state-c R)]
        [l_h (state-hmin L)]
        [r_h (state-hmin R)])
    (state
     (and l_cr (>= (- l_c r_h) 0))
     (+ l_c r_c)
     (min l_h r_h))))

(define non_sym_string (vector #t #t #f #f #t #t #f #f #f #f))
(define l (bal-f non_sym_string 0 3))
(define r (bal-f non_sym_string 3 10))
(define t (bal-f non_sym_string 0 10))
(define j (join l r))

(define left (bal-f sym_string 0 split))
(define right (bal-f sym_string split len))
(define total (bal-f sym_string 0 len))
(define join_res (join left right))



(define odot
  (synthesize
   #:forall (list a0 a1 a2 a3 a4 a5 a6 a7 len)
   #:guarantee (assert (eq? total join_res))))

(if (sat? odot) (print-forms odot) (core odot))
