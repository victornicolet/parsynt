#lang racket

(require (prefix-in c: c)
         "../lib/utils.rkt"
         "./check.rkt"
         "./pprint.rkt"
         "./exceptions.rkt"
         "../lib/utils.rkt")

(provide loops (prefix-out L: Globals) (prefix-out L: Typedefs) Loops)

(define (loops program)
  (flatten (map analyse-toplvl program)))

(define Globals (make-hash))
(define Typedefs (make-hash))
(define Loops (make-hash))

(struct loop-with-context (defined-in
                            defined-out
                            only-loc
                            stmt)
  #:extra-constructor-name make-lwc
  #:transparent)

(define (analyse-toplvl stmt-or-decl)
  (match stmt-or-decl
    ;; Declarations -> 
    [(c:decl:typedef src type decls)   
     (hash-set! Typedefs (check-typedef type decls src) stmt-or-decl)]

    [(c:decl:vars src storage-class type decls) 
     (for-each 
      (lambda (decl) 
        (hash-set-pair! Globals
         (check-vardecl decl storage-class type src)))
      decls)]

    [(c:decl:function src stg-cls inline? ret-ty decl preamble body)
     (extract-loop stmt-or-decl)]
    
    [(c:decl _) (raise (toplevel-exn #f "bad declaration" (current-continuation-marks)))]
    [(c:stmt _) (raise (toplevel-exn #f "statement" (current-continuation-marks)))]
    [_ (raise (toplevel-exn #f "unrecognized input" (current-continuation-marks)))]
    ))


(define/contract (extract-loop stmt-or-decl locals) 
  (-> (or/c c:stmt? c:decl?) any)
  (let ([res
         (match stmt-or-decl
           ;; Loops
           [(or (c:stmt:for _ _ _ _ _)
                (c:stmt:while _ _ _)
                (c:stmt:do _ _ _))  stmt-or-decl]
           ;; Search sub-blocks
           [(c:decl:function src _ _ _ _ _ body)
            (error (format "~a - Inner function definition in ~a")
                   (sprint-src src) (sprintc body))]
           [(c:stmt:label _ _ body) '()]
           [(or (c:stmt:case _ _ body) 
            (c:stmt:block _ body)
            (c:stmt:switch _ _ body)
            (c:stmt:default _ body))
            (cond
              [(list? body) 
               (foldl 
                (lambda (v x) (extract-loop  body)))])]
           ;; Statements or declarations without sub-blocks
           [_ #f])])
    (if (list? res) (remove #f (flatten res))
        (if (eq? res #f) '() (list res)))))
                                              

