#lang racket

(require c)

(provide extract-for-loops)

(define (extract-for-loops loop-list cprogram)
  (foldl extract-from-decl loop-list cprogram))


(define (extract-from-decl loop-list decl)
  (match decl 
    [(decl:function _ _ _ _ decl-ctx _ _)
     (begin
       (print-declarator-context decl-ctx)
       (extract-in-func loop-list decl))]
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

(define (print-declarator-context decl-ctx)
 (match decl-ctx
   [(decl:declarator _ id type initializer) (print-id id)]))

(define (print-id id)
  (match id
    [(id:var _ name-symbol) (printf "~s:~s" "var:" (symbol->string name-symbol))]
    [(id:label _ name-symbol) (printf "~s:~s" "label:" (symbol->string name-symbol))]
    [(id:op _ name-symbol) (printf "~s:~s" "op:" (symbol->string name-symbol))]
    [(id:storage _ storage-class) (printf "~s:~s" "class:" storage-class)]
    [(id:inline _) (print "inline")]
    [_ (print "unrecognized id")]
  ))
