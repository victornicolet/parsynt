#lang racket

(require (except-in c struct)
         racket/contract/region
         racket/contract
         "../lib/utils.rkt"
         "./pprint.rkt")

(provide cfstmt cfstmt?
         cfstmt:case cfstmt:default cfstmt:block cfstmt:expr cfstmt:if
         cfstmt:switch cfstmt:while cfstmt:do cfstmt:for cfstmt:goto
         cfstmt:continue cfstmt:break cfstmt:label cfstmt:empty cfstmt:return
         gen-empty-block
         cf-block? cf-node? cf-exit? cf-block? cf-loop?
         link-stmts! block-add-stmt!
         hash-stmt stmt-name)

;; This C intermediary language is en enriched ast representation
;; of the ast in c-utils. This allows to build he control flow graph and ..,

;; We keep the same structs except for the statements, they need additional
;; fields for keeping informations about the successor/ predecessor ine the 
;; CFG
;; Block statements are just blocks, a list of statements
(define (cf-block? stmt)
  (and (cfstmt? stmt) (cfstmt:block? stmt)))

;; Regular control flow nodes
(define (cf-node? stmt)
  (and (cfstmt? stmt)
       (or (cf-exit? stmt)
           (cf-loop? stmt)
           (cfstmt:case? stmt)
           (cfstmt:if? stmt)
           (cfstmt:label? stmt)
           (cfstmt:switch? stmt))))

;; Loop nodes
(define (cf-loop? stmt)
  (and (cfstmt? stmt)
       (or (cfstmt:for? stmt)
           (cfstmt:while? stmt)
           (cfstmt:do? stmt))))

;; Exit control flow nodes. A block can have several
;; exit points but only one entry point
(define (cf-exit? stmt)
  (and (cfstmt? stmt)
       (or (cfstmt:return? stmt)
           (cfstmt:break? stmt)
           (cfstmt:goto? stmt)
           (cfstmt:continue? stmt))))

;; A C statement.  src : (or/c src? #f)
;; succs contains the successors in the CFG and preds the predecessors
(struct cfstmt (src succs preds) 
  #:mutable #:transparent)

;; A labeled statement.
(define-struct/contract	(cfstmt:label cfstmt)
  ((label id:label?)) #:mutable)

;; A case statement.
(define-struct/contract (cfstmt:case cfstmt)
  ((expr expr?)) #:mutable)
;; A default statement.
(struct	 cfstmt:default cfstmt () #:mutable)

;; A compound statement.
(define-struct/contract (cfstmt:block cfstmt)
  ((items (listof (or/c decl? cfstmt?)))) #:mutable)

;; An expression statement.
(define-struct/contract	(cfstmt:expr cfstmt)
  ((expr expr?)) #:mutable)

;; An if statement.
(define-struct/contract	(cfstmt:if cfstmt)
  ((test expr?)) #:mutable)

;; A switch statement.
(define-struct/contract	(cfstmt:switch cfstmt) 
  ((test expr?)) #:mutable)

;; A while statement.
(define-struct/contract	(cfstmt:while cfstmt)
  ((test expr?)) #:mutable)

;; A do-while statement.
(define-struct/contract  (cfstmt:do cfstmt)
  ((test expr?)) #:mutable)



;; A for statement.
(define-struct/contract	 (cfstmt:for cfstmt)
  ((init (or/c expr? decl? #f))
   (test (or/c expr? #f))
   (update (or/c expr? #f))))

;; A goto statement.
(define-struct/contract	(cfstmt:goto cfstmt) ((label id:label?)))

;; A continue statement.
(struct cfstmt:continue cfstmt ())

;; A break statement.
(struct	cfstmt:break cfstmt ())

;; A return statement.

(define-struct/contract	(cfstmt:return cfstmt) ((result (or/c expr? #f))))

;; Empty statement
(struct	cfstmt:empty cfstmt ())


;; Add a statement to a block, and return the current block.
(define/contract (block-add-stmt! block stmt)
  (-> cf-block? (or/c cfstmt? decl?) cf-block?)
  (let ([items (cfstmt:block-items block)])
    (set-cfstmt:block-items! block (c-append items stmt))
    block))

;; Link two statements together and return the second statement.
(define/contract (link-stmts! stmt1 stmt2)
  (-> cfstmt? cfstmt? cfstmt?)
  (let ([preds (cfstmt-preds stmt2)]
        [succs (cfstmt-succs stmt1)])
    (set-cfstmt-preds! stmt2 (c-append preds stmt1))
    (set-cfstmt-succs! stmt1 (c-append succs stmt2))
    stmt2))

;; Generate an empty block. Useful for preparing the outgoing
;; edge of a block.
(define/contract (gen-empty-block src)
  (-> src? cfstmt:block?)
  (cfstmt:block src '() '() '()))

;; A block is empty if its body is empty
(define/contract (is_empty_block? stmt)
  (-> cfstmt? boolean?)
  (and (cf-block?)
       (empty? (cfstmt:block-items stmt))))

(define/contract (is_collapsable_block? stmt)
  (-> cfstmt? boolean?)
  (and (is_empty_block? stmt)
       (<= (length (cfstmt-preds stmt)) 1)))

(define/contract (collapse block)
  (-> cfstmt:block? cfstmt?)
  block
  )

(define/contract (stmt-name stmt)
  (-> cfstmt? string?)
  (cond
    [(cfstmt:block? stmt) "block"]
    [(cfstmt:expr? stmt) "expr"]
    [(cfstmt:if? stmt) "if"]
    [(cfstmt:switch? stmt) "switch"]
    [(cfstmt:case? stmt) "case"]
    [(cfstmt:default? stmt) "default"]
    [(cfstmt:break? stmt) "break"]
    [(cfstmt:for? stmt) "for"]
    [(cfstmt:while? stmt) "while"]
    [(cfstmt:do? stmt) "do"]
    [(cfstmt:return? stmt) "return"]
    [(cfstmt:goto? stmt) "goto"]
    [(cfstmt:label? stmt) "label"]
    [(cfstmt:continue? stmt) "continue"]
    [else "NOT A STATEMENT"]))

(define/contract (hash-src src)
  (-> src? string?)
  (format "~v~v~v" (src-start-offset src) (src-end-offset src) (src-path src)))

(define/contract (hash-stmt stmt)
  (-> cfstmt? string?)
  (format "~a~a" (hash-src (cfstmt-src stmt)) (stmt-name stmt)))
