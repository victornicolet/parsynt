#lang racket

(require c
         racket/list
         "./pprint.rkt")

(provide check-typedef check-vardecl check-switch-body)



(define/contract (check-declarator-context decl ty)
  (-> decl? type? (or/c decl? #f))
  (if (and (complete-type? ty) (declarator-context? decl))
      (apply-declarator-context decl ty)
      (error (format "Not a declarator context : type ~a declarator ~a" 
                     (sprintc ty) (sprintc decl)))))

;; Check the consistency of the typedefs and returns a list of typedefs,
;; one for each declarator in the orignal typedef
(define (check-typedef ty decls src)
  (if 
   (not (complete-type? ty))
   (error (format "~a - Expected a complete type in typedef, 
but received ~a instead." (sprintc ty) (sprint-src src)))
   (cond
     [(list? decls)
      (map 
       (lambda (decl)
         (make-decl:typedef  src ty 
                             (list (check-declarator-context decl ty))))
       decls)]
     [else (error
            (format "~a - Typedef check failed because there is no declarators."
                    (sprint-src src)))])))

(define (check-vardecl decl stg-cls ty src)
  (match decl
    [(decl:declarator _ id type initializer)
       ;; type must be a type context 
       (if 
        (not (type-context? type))
        (error (format "Expected a type context at ~a" (sprint-src src)))
        (if 
         (not (complete-type? ty))
         (error (format "Expected a complete type at ~a" (sprint-src src)))
         (cons
          (id:var-name id)
          (make-decl:vars src stg-cls ty
                            (check-declarator-context decl ty)))))]
    [ _ (error (format "Not a type declarator at ~a" (sprint-src src)))]))


;; Checks if the body of a switch is either a block with case/default
;; statements inside or a single default/case statement. It returns the
;; list with one or more items.
(define (check-switch-body stmt)
  (match stmt
    [(stmt:block src items)
     (cond
       [(list? items)
        (cond
          [(empty? items) (list)]
          [else (if
                 (andmap (lambda (item) (or (stmt:case? item)
                                            (stmt:default? item)))
                         items)
                 items
                 (list))])])]
    [(or (stmt:case _ _ _)
         (stmt:default _ _)) (list stmt)]))
