#lang rosette

(require rosette/lib/synthax
         racket/match
         "../utils.rkt")

;; A polynom is a list of factors : 
;; (polynom '(1 2 3)) => x^2 + 2*x + 3
(struct polynom (factors))


(define (interpret-polynom poly x)
  (let ([factors (reverse (polynom-factors poly))])
    (define (aux-eval-poly facs x)
      (let ([len (length facs)])
      (cond
        [(= len 0) 0]
        [(= len 1) (car facs)]
        [else (+ (car facs) (* x (aux-eval-poly (cdr facs) x)))])))
    (aux-eval-poly factors x)
    ))


;; A polynomial LMAD is a LMAD where each f_k is represented
;; by a polynom
(struct poly-LMAD (polynoms tau))

(define (interpret-poly-lmad lmad ilist)
  (let ([plys (poly-LMAD-polynoms lmad)]
        [tau (poly-LMAD-tau lmad)])
  (foldl (lambda (i poly acc)
           (+ acc (interpret-polynom poly i)))
         tau ilist plys)))


;; Try to find a polynomial LMAD matching a given subscript
(define-synthax PolyLMAD 
  ([(PolyLMAD [c ...] p len) (poly-LMAD (PolyList [c ...] p len)
                                        (FactorExpr [c ...]))]))

(define-synthax (PolyList [c ...] p len)
  #:base (list (polynom (FactorList [c ...] p)))
  #:else (cons (polynom (FactorList [c ...] p))
               (PolyList [c ...] p (sub1 len))))

(define-synthax (FactorList [c ...] deg)
  #:base (list (FactorExpr c ...))
  #:else (cons (FactorExpr c ...) 
               (FactorList [c ...] (sub1 deg))))

(define-synthax FactorExpr
  ([(FactorExpr c ...) (choose (+ (choose c ... (??))
                                 (choose c ... (??)))
                              c ... (??))]))

(define (lmad1 a b ilist)
  (interpret-poly-lmad (PolyLMAD [a b] 2 1) ilist))

(define (expr a b ilist)
  (let ([i (car ilist)]
        [j (cadr ilist)])
    (+ (* i (+ i a)) (+ j (* i i)) 2 (* b j) (+ j j))))

(define (correct? lmad ini a b ilist)
  (assert (eq? (lmad a b ilist) (ini a b ilist))))

(define-symbolic i1 i2 c1 c2 c3 integer?)

(define sol
  (time
   (synthesize
    #:forall (list i1 i2 c2 c3)
    #:guarantee (correct? lmad1 expr c2 c3 (list i1 i2)))))

(define (solution a b ilist)
  (eval (syntax->datum (car (generate-forms sol))))
        (lmad1 a b ilist))
