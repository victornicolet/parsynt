#lang rosette

(require consynth/lib/synthax/constructors
         consynth/lib/synthax/expressions
         rosette/lib/synthax
         rosette/query/debug
         )

;; Sum elts
(define (sum x) (foldl + 0 x))
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
(define (mps-RL x) (foldr (lambda (v l) (max 0 (+ v l))) 0 x))
;; From left to right
(define (mps-LR x) (let ([rvx (reverse x)]
                         [rvs (cdr (append (reverse (pre-sum x)) (list 0)))])
                     (define (mps-aux rx rs)
                       (if (<= (length rx) 0)
                           0
                           (max (mps-aux (cdr rx) (cdr rs))
                                (+ (car rx) (car rs)))))
                     (mps-aux rvx rvs)))

(define (mps-and-sum x) (cons (mps-RL x) (sum x)))


(define/debug (mps-join L R)
  (let ([mpsL (car L)] [sL (cdr L)][mpsR (car R)][sR (cdr R)])
    (cons (car (mps-and-sum (list mpsL (- sL mpsL) mpsR (- sR mpsR)))) (+ sL sR))))

(define-values (l01 l02) (values (list 1 -2 3 -2 -17 3) (list 2 1 5 0 -9 0)))

(define (synth-mps-join L R)
  (let ([mpsL (car L)] [sL (cdr L)][mpsR (car R)][sR (cdr R)])
    (cons (Expr mpsL sR sL mpsR 2) (Expr mpsL mpsR sL sR 2))))

(define-syntax problem
  (syntax-rules ()
    [(problem join ll rl) (eq? (mps-and-sum (append ll rl))
                                (join (mps-and-sum ll) (mps-and-sum rl)))]))


(define-symbolic li0 li1 li2 li3 integer?)
(define-symbolic li5 li6 li7 li8 integer?)

(define-values (l1 l2) (values (list li0 li1 li2 li3)
                               (list li5 li6 li7 li8)))

(if (unsat? (verify (problem mps-join l1 l2)))
    (display "Given join is not correct !\n") 
    (display "Given join is correct.\n"))

(define odot
  (time
   (synthesize
    #:forall (list li0 li1 li2 li3  li5 li6 li7 li8 )
    #:guarantee (assert (problem mps-join l1 l2)))))
