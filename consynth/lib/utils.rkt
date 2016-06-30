#lang racket

(require (for-syntax syntax/struct syntax/parse racket/syntax))


(provide (all-defined-out))

(define (map-apply func items)
  (if (list? items) (map func items) (func items)))

(define-for-syntax (map2 f a b acc)
  (cond
    [(or (eq? a '()) (eq? b '())) acc]
    [else (map2 f (cdr a) (cdr b)
                (append acc (list (f (car a) (car b)))))]))

(define (hash-set-pair! hsh pair)
  (hash-set! hsh (car pair) (cdr pair)))

(define/contract (c-append l x)
  (-> (or/c list? any/c) any/c list?)
  (if (and (list? l) (not (empty? l)))
      (append l (list x))
      (list x)))

;; Increment/decrement statelike variables
(define-syntax-rule (pre-incr x) (begin (set! x (add1 x)) x))
(define-syntax-rule (post-incr x) (let ([xpre x]) (set! x (add1 x)) xpre))

;; Helper macro for struct definitons
(define-for-syntax (get-1st-every-triplet tl acc)
  (if (<= (length tl) 3)
      (append acc (list (car tl)))
      (get-1st-every-triplet (cddr tl) (append acc (list (car tl))))))

;; Syntax manipulation helpers
(define-for-syntax (unpack stx)
  (if (list? stx)
      (map unpack stx)
      (syntax-e stx)))

(define-for-syntax (pack stx-list)
  (datum->syntax #f stx-list))

; Careful when playing with identifiers and converting from syntax to datum,
; (format-id #f ...will yield an error is using some identifier declared outside
;                   the macro.
; Don't forget to add
; (format-id stx ... if a stx object from the toplevel macro is avialable

(define-syntax (LetStructFieldnames stx)
  (syntax-parse stx
    [(let-st structname s (fieldnames ...) body)
     (with-syntax
       ([(field-assignments ...)
         (map (lambda (fname)
                (with-syntax
                  ([(ident fieldn) (list
                                    (format-id stx "~a-~a" #'structname fname)
                                    (pack fname))])
                  #'(fieldn (ident s))))
             (unpack #'(fieldnames ...)))])
       #'(let (field-assignments ...) body))]))

(struct state (a b c))
(define s (state 1 2 3))

(define (test) (LetStructFieldnames state s (a b c) #t))
(assert (test))
