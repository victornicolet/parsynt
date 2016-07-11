#lang rosette

(require consynth/lib/synthax/constructors
         consynth/lib/synthax/expressions
         rosette/lib/synthax
         rosette/query/debug
         )

;; Reduce f on list l with neutral element
(define (reduce f l n)
  (let ([len (length l)])
    (if (> len 2)
        (begin
          (define-values (lr ll) (split-at l (round (/ len 2))))
          (f (reduce f lr n) (reduce f ll n)))
        (if (= len 2) (f (car l) (cadr l))
            (if (= len 1) (f (car l) n) n)))))

;; Sum elts
(define (sum x sum0) (foldl + sum0 x))

;; List of prefix sums
(define (pre-sum x)
  (letrec ([aux (lambda (l s r)
                  (let ([ns (+ s (car r))])
                    (if (<= (length r) 1)
                        (append l (list ns))
                        (aux (append l (list ns))
                             ns (cdr r)))))])
    (aux '() 0 x)))

;; Maximum prefix sum, scanning list from right to left
(define (mps-RL x mps0) (foldr (lambda (v l) (max 0 (+ v l))) mps0 x))
;; From left to right
(define (mps-LR x) (let ([rvx (reverse x)]
                         [rvs (cdr (append (reverse (pre-sum x)) (list 0)))])
                     (define (mps-aux rx rs)
                       (if (<= (length rx) 0)
                           0
                           (max (mps-aux (cdr rx) (cdr rs))
                                (+ (car rx) (car rs)))))
                     (mps-aux rvx rvs)))

(define (mps-and-sum x) (cons (mps-RL x 0) (sum x 0)))

(define (mpss x [init-state (cons 0 0)])
  (cons (mps-RL x (car init-state)) (sum x (cdr init-state))))


(define (f x) (cons (max x 0) x))

;; Mpd join takes as arguments two lists, where each of the first elements of
;; the lists is the maximum-prefix-sum of the sate and the second one is the
;; sum so far. Then returns a list containing (mps, sum).
(define (mps-join L R)
  (let ([mpsL (car L)] [sL (cdr L)][mpsR (car R)][sR (cdr R)])
    (cons (car (mps-and-sum (list
                             ((choose - +)
                              (choose mpsL sL mpsR sR (??))
                              (choose mpsL sL mpsR sR (??)))

                             ((choose - +)
                              (choose mpsL sL mpsR sR (??))
                              (choose mpsL sL mpsR sR (??)))

                             ((choose - +)
                              (choose mpsL sL mpsR sR (??))
                              (choose mpsL sL mpsR sR (??)))

                             ((choose - +)
                              (choose mpsL sL mpsR sR (??))
                              (choose mpsL sL mpsR sR (??))))))
          (+ sL sR))))


(define-values (l01 l02) (values
                          (list 1 -2 3 -2 -17 3 -10 4)
                          (list 2 1 5 0 -9 0)))

;; -----------------------------------------------------------------------------
;; Join expressed as the homomorpihsm h(x++y) = h(x) # h(y).
(define-syntax problem
  (syntax-rules ()
    [(problem join ll rl) (eq? (mps-and-sum (append ll rl))
                                (join (mps-and-sum ll) (mps-and-sum rl)))]))


(current-bitwidth #f)

(define-symbolic li0 li1 li2 li3 li4 integer?)
(define-symbolic li5 li6 li7 integer?)

(define-values (l1 l2) (values (list li0 li1 li2 li3 li4)
                               (list li5 li6 li7)))

(if (unsat? (verify (assert (problem mps-join l1 l2))))
    (display "Given join is not correct !\n")
    (display "Given join is correct.\n"))

(define odot
  (time
   (synthesize
    #:forall (list li0 li1 li2 li5 li6 li3 li4 )
    #:guarantee (assert (problem mps-join l1 l2)))))

(if (sat? odot) (print-forms odot) (core odot))

;; Output ;
;; Given join is correct.
;; cpu time: 533 real time: 62406 gc time: 29
;; /home/victorn/repos/consynth/examples/synthesis/loops/maximum-prefix-sum.rkt:48:0
;; '(define (mps-join L R)
;;    (let ((mpsL (car L)) (sL (cdr L)) (mpsR (car R)) (sR (cdr R)))
;;      (cons
;;       (car (mps-and-sum (list (+ mpsL 0) (- 0 mpsL) (+ 0 sL) (+ mpsR 0))))
;;       (+ sL sR))))

;; -----------------------------------------------------------------------------
;; Join problem in its "imperative" form, where the join appears on each side of
;; the = : s # B(s',i) = B(s#s',i) where s, s' are ANY state and not only a
;; state resulting from the application of a body.
(clear-asserts!)
(define-symbolic mps1 sum1 mps2 sum2 a integer?)

(define s0-prim (cons 0 0))
(define state1 (cons mps1 sum1))
(define state2 (cons mps2 sum2))

(assert (>= 0 mps1))
(assert (>= 0 mps2))

(define one-iter-list (list a))
(define odot-prim
  (time
   (synthesize
    #:forall (list mps1 sum1 mps2 sum2 a)
    #:guarantee (assert
                 (eq? (mps-join state1
                                (mpss one-iter-list state2))
                      (mpss
                       one-iter-list (mps-join state1 state2)))))))

;; Timeout after running the solver for 10 minutes.

(if (sat? odot-prim) (print-forms odot-prim) (core odot-prim))
