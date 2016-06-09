#lang racket

(require "./cil.rkt"
         (except-in c struct)
         "./pprint.rkt"
         "./check.rkt"
         "./exceptions.rkt"
         "../lib/utils.rkt")

;; Computes the control flow graph for a C program by translating
;; the input AST fromc-utils into statements with predecessors 
;; and successors

(define start-id 0)
(define await-break #f)
(define break #f)

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
         (link-stmts!
          (foldl
           (lambda (case-stmt prev-block)
             (case/default-link switch-node case-stmt prev-block next-body))
           (switch-node)
           (check-switch-body body))
          next-body)))]
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
    ;; In the first pass all continue/return statements are only 
    ;; translated to the intermediary language and inserted in the statement
    ;; list of the current block.
    ;; We will add the necessary edges in a second pass over the graph,
    ;; linking the continue/return statements to the successor 
    ;; of a parent, depending on the cases. This will also allow dead-code
    ;; elimination
    [(stmt:continue src) 
     (block-add-stmt! current-block (cfstmt:continue src '() '()))]
    [(stmt:break src)
     (if await-break
         (begin
           (set! await-break #f)
           (set! break #t)
           (block-add-stmt! current-block (cfstmt:break src '() '())))
         (raise (unexpected-exn "break" (current-continuation-marks))))]
    [(stmt:return src expr)
     (block-add-stmt! current-block (cfstmt:return src '() '()) expr)]
    ;; Loop statements.
    ;; The loop-back edge from the end of the loop body to the test node 
    [(stmt:while src test body)
     (let ([while-body (cfg-block body)]
           [while-node (cfstmt:while src '() '() test)]
           [next-block (gen-empty-block src)])
       (begin
         (link-stmts! current-block while-node)
         (link-stmts! while-node while-body)
         (link-stmts! while-body while-node)
         (link-stmts! while-node next-block)))]
    ;; The do node is a little bit different, the current block is directly
    ;; linked to the body of the loop, the test and back edge is created 
    ;; after.
    [(stmt:do src body test)
     (let ([do-body (cfg-block body)]
           [do-node (cfstmt:do src '() '() test)]
           [next-block (gen-empty-block src)])
       (begin
         (link-stmts! current-block do-body)
         (link-stmts! do-body do-node)
         (link-stmts! do-node do-body)
         (link-stmts! do-node next-block)))]
    ;; The for statement is only a special case of the while loop.
    [(stmt:for src ini test update body)
     (let ([for-body (cfg-block body)]
           [for-node (cfstmt:for src '() '() ini test update)]
           [next-block (gen-empty-block)])
       (begin 
         (link-stmts! current-block for-node)
         (link-stmts! for-node for-body)
         (link-stmts! for-body for-node)
         (link-stmts! for-node next-block)))]
    
    ;; Labels and gotos are treated seprarately
    ;; NOT YET IMPLEMENTED
    [(or (stmt:label src _ _)
         (stmt:goto  src _)) (error (format "Unsupported expression in ~a
 (label or goto)." (sprint-src src)))]

    ;; Declarations in blocks

 
    [_ current-block]))
          
          
            
;; This functions links a switch node with a statement,
;; provided this statement is a case/default statement. The case
;; statement is transformed into a case node and a body,
;; this body is then linked to the next case of the switch.
(define (case/default-link switch-node stmt prev-case if-break)
  (let
      ([stmt-case-body 
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
    (set! await-break #t)
    (let ([case-body (cfg-block stmt-case-body)])
      (begin
        (link-stmts! switch-node case-def-node)
        (link-stmts! prev-case case-def-node)
        (link-stmts! 
        (cond
          [break 
           (begin
             (set! break #f)
             (link-stmts! case-body if-break)
             case-def-node)]
          [else
           case-body]))))))
