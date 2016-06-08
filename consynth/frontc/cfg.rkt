#lang racket

(require (prefix-in c: c))

; Computes the control flow graph for a C program

(define start-id 0)

(struct func-node (entry ret-stmt)
  #:extra-constructor-name make-fnode)
(struct block-node (next break cont rlabels))


(define (compute-cfg program)
  (cond
    [(list? program) (filter-map all-stmts program)]
    [else '()]))


(define (all-stmts stmt-or-decl)
  (match stmt-or-decl
    [(c:decl:function src _ _ _ _ _ body)
     (func-node (cfg-stmts body))
     ]
    [_ #f]))


(define (cfg-stmts body) body)
