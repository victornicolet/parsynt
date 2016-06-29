#lang racket

(require rosette/safe
         syntax/struct)

(provide (all-defined-out))

;; Macros generating symbolic definitions

(define-syntax-rule (Integers id ...) (define-symbolic id ... integer?))

(define-syntax-rule (Reals id ...) (define-symbolic id ... real?))

(define-syntax-rule (Booleans id ...) (define-symbolic id ... boolean?))

;; Read-only arrays are just functions from integers to another type
(define-syntax-rule (RoArray (id ...) type)
  (define-symbolic id ... (~> integer? type)))

;; Helper macro for struct definitons
(define-for-syntax (get-1st-every-triplet triplet-list)
  (define (aux tl acc)
    (if (<= (length tl) 3)
        (append acc (car tl))
        (aux (cdddr tl) (append acc (car tl)))))
  (aux triplet-list '()))


(define-syntax (LetFieldName stx)
  (syntax-case stx ()
    [(_ structname (fieldnames ...))
     (with-syntax
       ([(top field-accessor ...)
         (get-1st-every-triplet
          (build-struct-names structname fieldnames ... #t #t))])


;; Macros generating function definitions body and join

(define-syntax-rule (DefineBody (vnames ...) (b ...))
     (lambda (vnames ...) (values b ...)))

(define-syntax-rule (DefineJoin (vnames ...) (b ...))
  (lambda (ll lr)
    ())
  )

(define-syntax (Synthesize stx)
  (syntax-case stx ()
    [(_ (symbs1 ...)(symbs2 ...) (symbs_r ...) (initials ...))
     (with-syntax
       ([(f1 ...) (generate-temporaries (symbs1 ...))]
        [(f2 ...) (generate-temporaries (symbs2 ...))])
       (synthesize
        #:forall (list symbs_r ... symbs1 ... symbs2)
        #:guarantee (assert
                     (and
                      (let-values ([(f1 ...) (body symbs1 ...)])
                        (let-values ([(join ...)))))
;; Test macros
(Integers i1 i2 i3)
(assert (map integer? (list i1 i2 i3)))
(Reals r1 r2 r3)
(assert (map real? (list r1 r2 r3)))
(Booleans b1 b2 b3)
(assert (map boolean? (list b1 b2 b3)))
(RoArray (a) integer?)
(assert (integer? (a i1)))
(define body (DefineBody (a b c) ((+ a b) (+ 1 b) (add1 c))))
(assert (let-values ([(a b c) (body 1 2 3)])(eq? (list a b c) (list 3 3 4))))
