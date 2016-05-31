#lang racket

(require c)

(provide loops)

(define (loops program)
  (remove #f (flatten (map extract-loop program))))

(define (extract-loop stmt-or-decl)
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
                (stmt:default _ body)) (map-or-apply extract-loop body)]
           ;; Statements or declarations without sub-blocks
           [_ #f])])
    (if (list? res) (remove #f (flatten res))
        (if (eq? res #f) '() (list res)))))

(define (map-or-apply func items)
  (if (list? items) (map func items) (func items)))



