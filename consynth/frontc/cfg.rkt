#lang racket

(require "./cil.rkt"
         (except-in c struct)
         "./pprint.rkt"
         "../lib/utils.rkt")

;; Computes the control flow graph for a C program by translating
;; the input AST fromc-utils into statements with predecessors 
;; and successors

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
    [(decl:function src _ _ _ _ _ body)
     (func-node (cfg-stmts body))
     ]
    [_ #f]))

;; If it's a block, create the empty cf-block and look at the items
;; if not, wrap the statement in a cf-block and treat the statement as 
;; the body of this wrapper block
(define (cfg-block stmt-block)
  (match stmt-block
    [(stmt:block src items) (cfg-stmts (gen-empty-block src) items)]
    [(stmt src) (cfg-stmts (gen-empty-block src) (list stmt-block))]))

;; Takes a body of stmts/decls and produces the last block(s) visited when
;; creating the graphs
(define (cfg-stmts current-block body)
   (match body
     [(cons hd tl) (cfg-stmts 
                    (cfg hd current-block)
                    tl)]
     ['() current-block]))

;; cfg replaces a stmt by a cfstmt, filling the in/out edges
;; by linking in the in edge provided, and is the statement is a control
;; statement, the out edge is the block-body. It returns either the block
;; with a new statement in it or a new block

(define (cfg stmt current-block)
  (match stmt
    [(stmt:block src items) 
     (link-stmts!  current-block (cfg-stmts (gen-empty-block src) items))]
    ;; The case statement is treated spearately in the switch body. 
    [(or 
      (stmt:case src _ body) 
      (stmt:default src body))
     (error (format "~a - CFG : case statement unexpected outside a switch"
                    (sprint-src src)))]
    ;; A switch statement will be connected to all the case statements 
    ;; and the default statement. 
    [(stmt:switch src expr body)
     (let ([next-body (gen-empty-block src)]
           [switch-node (cfstmt:switch src '() '() expr)])
       (begin 
         (link-stmts! current-block switch-node)
         (map-apply
          (lambda (case-stmt)
            (case/default-link switch-node case-stmt next-body))
          body)))]
    ;; The if node is linked to one or two blocks, depending on the
    ;; existence of an alt branch in the original body, then an empty 
    ;; block is returned
    [(stmt:if src expr cont alt)
     (let ([if-node (cfstmt:if src '() '() expr)]
           [cont-block (cfg-block cont)]
           [alt-block (if (alt) (cfg-block alt) #f)]
           [next-body (gen-empty-block src)])
       (begin
         (link-stmts! current-block if-node)
         (link-stmts! if-node cont-block)
         (cond [(alt-block) (begin
                              (link-stmts! if-node alt-block)
                              (link-stmts! alt-block next-body))])
         (link-stmts! cont-block next-body)))]
    ;; In the first pass all continue/break statements are only translated
    ;; to the intermediary language and inserted in the statement list of the
    ;; current block.
    ;; We will add the necessary edges in a second pass over the graph,
    ;; linking the continue/break/return statements to the successor 
    ;; of a parent, depending on the cases. This will also allow dead-code
    ;; elimination
    [(stmt:continue src) (block-add-stmt! current-block (cfstmt:continue src '() '()))]
    [(stmt:break src) (block-add-stmt! current-block (cfstmt:break src '() '()))]
    [(stmt:return src expr)  (block-add-stmt! current-block (cfstmt:return src '() '()) expr)]
    ;; Loop statements.
    ;; TODO 
    [_ current-block]))
          
          
            
;; This functions links a switch node with a statement,
;; provided this statement is a case statement. The case
;; statement is transformed into a case node and a body,
;; this body is then linked to the output block of the switch
(define (case/default-link switch-node stmt out-node)
  (let
      ([case-body 
        (cfg-block 
         (match stmt 
           [(or (stmt:case _ _ body)
                (stmt:default _ body)) body]
           [_ (error (format
                      "CFG : switch statement expects
 case statements in its body"))]))]
       [case-def-node 
        (match stmt
          [(stmt:case src expr body)
           (cfstmt:case src '() '() expr)]
          [(stmt:default src body)
           (cfstmt:default src '() '() expr)])])
    (begin
      (link-stmts! switch-node case-def-node)
      (link-stmts! case-def-node case-body)
      (link-stmts! case-body out-node))))
