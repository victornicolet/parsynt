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

(define (f x) (cons (max x 0) x))

(define (mps-join L R)
  (let ([mpsL (car L)] [sL (cdr L)][mpsR (car R)][sR (cdr R)])
    (cons (car (mps-and-sum (list ((choose - +) (choose mpsL sL mpsR sR (??))  (choose mpsL sL mpsR sR (??)))
                                   ((choose - +) (choose mpsL sL mpsR sR (??))  (choose mpsL sL mpsR sR (??)))
                                   ((choose - +) (choose mpsL sL mpsR sR (??))  (choose mpsL sL mpsR sR (??)))
                                   ((choose - +) (choose mpsL sL mpsR sR (??))  (choose mpsL sL mpsR sR (??))))))
          (+ sL sR))))


(define-values (l01 l02) (values (list 1 -2 3 -2 -17 3 -10 4) (list 2 1 5 0 -9 0)))


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
