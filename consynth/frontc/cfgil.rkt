#lang racket

(require (except-in c struct)
         racket/contract/region
         racket/contract)

(provide cfstmt
         cfstmt:case cfstmt:default cfstmt:block cfstmt:expr cfstmt:if cfstmt:switch
         cfstmt:while cfstmt:do cfstmt:for cfstmt:goto cfstmt:continue cfstmt:break
         cfstmt:label cfstmt:empty)

;; This C intermediary language is en enriched ast reprensentation
;; of the ast in c-utils. This allows to build he control flow graph and ..,

;; We keep the same structs except for the statements, they need additional
;; fields for keeping informations about the successor/ predecessor ine the 
;; CFG

;; A C statement.  src : (or/c src? #f)
;; succs contains the successors in the CFG and preds the predecessors
(struct cfstmt (src succs preds))
;; (define cfstmt/c
;;   (or/c #f
;;         (struct/dc cfstmt
;;                    [src (or/c src? #f)]
;;                    [succs #:lazy (or/c (listof (recursive-contract cfstmt/c #:chaperone)) #f)]
;;                    [preds #:lazy (or/c (listof (recursive-contract cfstmt/c #:chaperone)) #f)]))

;; A labeled statement.
(define-struct/contract	(cfstmt:label cfstmt) ((label id:label?)
                                               (cfstmt cfstmt?)))

;; A case statement.
(define-struct/contract (cfstmt:case cfstmt) ((expr expr?)
                                              (cfstmt cfstmt?)))
;; A default statement.
(define-struct/contract	 (cfstmt:default cfstmt) ((cfstmt cfstmt?)))

;; A compound statement.
(define-struct/contract (cfstmt:block cfstmt)
  ((items (listof (or/c decl? cfstmt?)))))

;; An expression statement.
(define-struct/contract	(cfstmt:expr cfstmt) ((expr expr?)))

;; An if statement.
(define-struct/contract	(cfstmt:if cfstmt)
  ((test expr?)
   (cons cfstmt?) 
   (alt (or/c cfstmt? #f))))

;; A switch statement.
(define-struct/contract	(cfstmt:switch cfstmt) 
  ((test expr?)
   (body cfstmt?)))

;; A while statement.
(define-struct/contract	(cfstmt:while cfstmt)
  ((test expr?)
   (body cfstmt?)))

;; A do-while statement.
(define-struct/contract  (cfstmt:do cfstmt)
  ((body cfstmt?) 
   (test expr?)))



;; A for statement.
(define-struct/contract	 (cfstmt:for cfstmt)
  ((init (or/c expr? decl? #f))
   (test (or/c expr? #f))
   (update (or/c expr? #f))
   (body cfstmt?)))

;; A goto statement.
(define-struct/contract	(cfstmt:goto cfstmt) ((label id:label?)))

;; A continue statement.
(define-struct/contract (cfstmt:continue cfstmt) ((cfstmt cfstmt?)))

;; A break statement.
(define-struct/contract	(cfstmt:break cfstmt) ((cfstmt cfstmt?)))

;; A return statement.

(define-struct/contract	(cfstmt:return cfstmt) ((result (or/c expr? #f))))

;; Empty statement
(struct	cfstmt:empty cfstmt ())
