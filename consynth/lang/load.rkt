#lang racket

(require c)

(provide extract-for-loops)

(define (extract-for-loops loop-list cprogram)
  (foldl extract-from-decl loop-list cprogram))


(define (extract-from-decl loop-list decl)
  (match decl 
    [(decl:function _ _ _ _ decl-ctx _ _)
       (extract-in-func loop-list decl)]
    [ _ loop-list]))

(define (extract-in-func loop-list func)
  (match func
    [(decl:function src stgclass inl rettype decl pre body)
     (match body
       [(stmt:block src items) 
        (foldl extract-stmt loop-list items)]
       [_ loop-list])]))

(define (extract-stmt stmt-or-decl l)
  (match stmt-or-decl 
    [(stmt:for _ ini test update body) (cons l stmt-or-decl)]
    [(stmt:while _ test body) (cons l stmt-or-decl)]
    [(stmt:do _ body test) (cons l stmt-or-decl)]
    [(stmt:switch _ test body) (extract-stmt l body)]
    [(stmt:if _ test stmt1 stmt2) (cons (extract-stmt l stmt1) (extract-stmt '() stmt2))]
    [(stmt:case _  expr stmt) (extract-stmt l stmt)]
    [_ l]))




