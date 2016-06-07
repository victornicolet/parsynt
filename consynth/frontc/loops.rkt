#lang racket

(require c
         "../lib/utils.rkt"
         "./check.rkt"
         "./exceptions.rkt"
         "../lib/utils.rkt")

(provide loops Globals Typedefs Loops)

(define (loops program)
  (flatten (map analyse-toplvl program)))

(define Globals (make-hash))
(define Typedefs (make-hash))
(define Loops (make-hash))


(define (analyse-toplvl stmt-or-decl)
  (match stmt-or-decl
    ;; Declarations -> 
    [(decl:typedef src type decls)   
     (hash-set! Typedefs (check-typedef type decls src) stmt-or-decl)]

    [(decl:vars src storage-class type decls) 
     (for-each 
      (lambda (decl) 
        (hash-set-pair! Globals
         (check-vardecl decl storage-class type src)))
      decls)]

    [(decl:function src stg-cls inline? ret-ty decl preamble body)
     (extract-loop stmt-or-decl)]
    
    [(decl _) (raise (toplevel-exn src "bad declaration" (current-continuation-marks)))]
    [(stmt _) (raise (toplevel-exn src "statement" (current-continuation-marks)))]
    [_ (raise (toplevel-exn src "unrecognized input" (current-continuation-marks)))]
    ))


(define/contract (extract-loop stmt-or-decl) (-> (or/c stmt? decl?) any)
  (let ([res
         (match stmt-or-decl
           ;; Loops
           [(or (stmt:for _ _ _ _ _)
                (stmt:while _ _ _)
                (stmt:do _ _ _)) stmt-or-decl]
           ;; Search sub-blocks
           [(or (decl:function _ _ _ _ _ _ body)
                (stmt:label _ _ body)
                (stmt:case _ _ body)
                (stmt:block _ body)
                (stmt:switch _ _ body)
                (stmt:default _ body)) (map-apply extract-loop body)]
           ;; Statements or declarations without sub-blocks
           [_ #f])])
    (if (list? res) (remove #f (flatten res))
        (if (eq? res #f) '() (list res)))))
                                              

