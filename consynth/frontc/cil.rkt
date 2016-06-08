#lang racket

(require (except-in c struct)
         racket/contract/region
         racket/contract
         "../lib/utils.rkt")

(provide cfstmt
         cfstmt:case cfstmt:default cfstmt:block cfstmt:expr cfstmt:if cfstmt:switch
         cfstmt:while cfstmt:do cfstmt:for cfstmt:goto cfstmt:continue cfstmt:break
         cfstmt:label cfstmt:empty cfstmt:return
         gen-empty-block
         cf-block? cf-node? cf-exit? cf-block?
         link-stmts! block-add-stmt!)

;; This C intermediary language is en enriched ast reprensentation
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
       (or (cfstmt:break? stmt)
           (cfstmt:case? stmt)
           (cfstmt:continue? stmt)
           (cfstmt:do? stmt)
           (cfstmt:for? stmt)
           (cfstmt:if? stmt)
           (cfstmt:label? stmt)
           (cfstmt:switch? stmt)
           (cfstmt:while? stmt))))

;; Exit control flow nodes. A block can have several
;; exit points but only one entry point
(define (cf-exit? stmt)
  (and (cfstmt? stmt)
       (or (cfstmt:return? stmt)
           (cfstmt:break? stmt)
           (cfstmt:goto? stmt))))

;; A C statement.  src : (or/c src? #f)
;; succs contains the successors in the CFG and preds the predecessors
(struct cfstmt (src succs preds) #:mutable)
;; (define cfstmt/c
;;   (or/c #f
;;         (struct/dc cfstmt
;;                    [src (or/c src? #f)]
;;                    [succs #:lazy (or/c (listof (recursive-contract cfstmt/c #:chaperone)) #f)]
;;                    [preds #:lazy (or/c (listof (recursive-contract cfstmt/c #:chaperone)) #f)]))

;; A labeled statement.
(define-struct/contract	(cfstmt:label cfstmt) ((label id:label?)) #:mutable)

;; A case statement.
(define-struct/contract (cfstmt:case cfstmt) ((expr expr?)) #:mutable)
;; A default statement.
(struct	 cfstmt:default cfstmt () #:mutable)

;; A compound statement.
(define-struct/contract (cfstmt:block cfstmt)
  ((items (listof (or/c decl? cfstmt?)))) #:mutable)

;; An expression statement.
(define-struct/contract	(cfstmt:expr cfstmt) ((expr expr?)) #:mutable)

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

(define/contract (block-add-stmt! block stmt)
  (-> cf-block? cfstmt? cf-block?)
  (let ([items (cfstmt:block-items block)])
    (set-cfstmt:block-items! (c-append items stmt))))

(define (link-stmts! stmt1 stmt2)
  (let ([preds (cfstmt-preds stmt2)]
        [succs (cfstmt-succs stmt1)])
    (begin
      (set-cfstmt-preds! stmt2 (c-append preds stmt1))
      (set-cfstmt-succs! stmt1 (c-append succs stmt2))
      stmt2 )))

(define (gen-empty-block src)
  (cfstmt:block src '() '() '()))

;; A block is empty if it has no successors and no statements
;; in its body.
(define (is_empty_block? stmt)
  (and (cf-block?)
       (empty? (cfstmt:block-items stmt))
       (empty? (cfstmt-succs stmt))))
