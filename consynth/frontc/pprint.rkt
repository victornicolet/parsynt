#lang racket

(require c
         racket/pretty racket/match)

(provide sprintc sprint-src)

; General interface for printing C programs 
(define (sprintc program)
  (match program
    [(expr _ ) (sprint-cexp program)]
    [(decl _ ) (sprint-decl program)]
    [(type _) (sprint-type program)]
    [(stmt _) (sprint-stmt program)]
    [(id _) (sprint-id program)]
    [_ (sprint-decl-list program)]))

; Printing C expressions
(define (sprint-cexp cexpr) 
  (match cexpr
    [(expr:ref _ id) (sprint-id id)]
    [(expr:int _ val qualifiers) (format "~a ~a" val 
                                         (sprint-qualifiers qualifiers))]
    [(expr:float _ val qualifiers) (format "~a ~a" val 
                                           (sprint-qualifiers qualifiers))]
    [(expr:char _ source wide?) (format "char ~a" source)]
    [(expr:string _ source wide?) (format "string ~a" source)]
    [(expr:compound _ type inits) (format "~a ~a" (sprint-type type)
                                          (sprint-inits inits)) ]
    [(expr:array-ref _ expr offset) (format "~a[~a]"
                                            (sprint-cexp expr)
                                            (sprint-cexp offset))]
    [(expr:call _ func args) (format "~a (~a)"
                                     (sprint-cexp func)
                                     (sprint-cexp-list args))]
    [(expr:member _ expr label) (format "~a.~a" 
                                        (sprint-cexp expr)
                                        (sprint-id label))]
    [(expr:pointer-member _ expr label) (format "~a -> ~a"
                                                (sprint-cexp expr)
                                                (sprint-id label))]
    [(expr:postfix _ expr op) (format "~a ~a" (sprint-cexp expr) (sprint-id op))]
    [(expr:prefix _ op expr) (format "~a ~a" (sprint-id op) (sprint-cexp expr))]
    [(expr:cast _ type expr) (format "~a(~a)" (sprint-type type) (sprint-cexp expr))]
    [(expr:sizeof _ term) (format "sizeof(~a)" (sprint-term term))]
    [(expr:unop _ op expr) (format "~a ~a" (sprint-id op) (sprint-cexp expr))]
    [(expr:binop _ lexpr op rexpr) (format "~a ~a ~a"
                                           (sprint-cexp lexpr)
                                           (sprint-id op)
                                           (sprint-cexp rexpr))]
    [(expr:assign _ lexpr op rexpr) (format "~a ~a ~a"
                                            (sprint-cexp lexpr)
                                            (sprint-id op)
                                            (sprint-cexp rexpr))]
    [(expr:begin _ left right) (format "~a;\n~a"
                                       (sprint-cexp left)
                                       (sprint-cexp right))]
    [(expr:if _ test conss alt) (format "~a?~a:~a" 
                                        (sprint-cexp test) 
                                        (sprint-cexp conss)
                                        (sprint-cexp alt))]
    [(expr src) ""]
    [#f ""]
    [_ (error (format "Received a bad expression : ~a" cexpr))]))




(define (sprint-cexp-list cexp-list)
  (match cexp-list
    [(cons a b) (format "~a, ~a" (sprint-cexp a) (sprint-cexp-list b))]
    ['() ""]
    [a (sprint-cexp a)]))

(define (sprint-compound element)
  (match element
    [(cons dtors ini) (format "~a ~a" 
                              (map sprint-designator dtor)
                              (sprint-init ini))]
    [ini (sprint-init ini)]))

(define (sprint-decl cdecl)
  (match cdecl
    [(decl:typedef _ type declarators)
     (format "typedef ~a ~a;\n" 
             (sprint-type type)
             (string-join (map sprint-decl declarators)))]
    [(decl:vars _ storage-class type declarators) 
     (format 
      "~a ~a ~a;\n"
      (sprint-id storage-class)
      (sprint-type type)
      (string-join (map sprint-decl declarators)))]
    [(decl:formal _ storage-class type declarator) 
     (string-join
      (list
       (sprint-id storage-class)
       (sprint-type type)
       (sprint-decl declarator ))
      " "
      #:after-last "")]
    [(decl:function _ storage-class inline? return-type declarator preamble body)
     (format "~a~a ~a ~a~a {\n~a}" 
             (if inline? "inline " "") (sprint-id storage-class)
             (sprint-type return-type)
             (sprint-decl declarator) (sprint-decl-list preamble)
             (indented (sprint-stmt body)))]
    [(decl:declarator _ id type initializer)
     (format "~a ~a~a"
             (sprint-id id)
             (sprint-type type)
             (sprint-init initializer))]
    [(decl:member-declarator _ id type initializer bit-size) (format "~a ~a ~a [~a]\n"
                                                                     (sprint-id id)
                                                                     (sprint-type type)
                                                                     (sprint-init initializer)
                                                                     (sprint-cexp bit-size))]
    [(decl:member _ type declarators) (format "~a ~a"
                                              (sprint-type type)
                                              (string-join (map sprint-decl declarators) 
                                                           ", " #:after-last ""))]
    [(decl src) ""]
    [(or '() #f) ""]
    [_ ""]))

(define (sprint-decl-list dlist)
  (match dlist
    [(cons a b) (string-join (list (sprint-decl a) (sprint-decl-list b)) "")]
    [a (sprint-decl a)]
    ['() ""]
    [_ (error "In sprint-decl-list, expected a list, a declaration or an empty list.")]))

(define (sprint-designator designator)
  (match designator
    [(dtor:array _ expr) (format "[~a]" (sprint-cexp expr))]
    [(dtor:member _ label) (format ".~a" (sprint-id label))]
    [(dtor src) ""]
    [_ (error "Unexpected argument, not a designator.")]))


(define (sprint-formals formals) 
  (string-join 
          (map
           (lambda (decl-or-id)
             (match decl-or-id
               [(decl:formal _ _ _ _) (sprint-decl decl-or-id)]
               [(id:ellipsis _) (sprint-id decl-or-id)]))
           formals)
          ", "))

(define (sprint-id id)
  (match id
    [(id:var _ name-symbol)  (symbol->string name-symbol)]
    [(id:label _ name-symbol) (symbol->string name-symbol)]
    [(id:op _ name-symbol) (symbol->string name-symbol)]
    [(id:storage _ storage-class) (format "~v" storage-class)]
    [(id:inline _) "inline"]
    [(id:qualifier _ name) (format "~v" name)]
    [(id:ellipsis _) "..."]
    [(id:star _) "*"]
    [#f ""]
    [_ (error (format "Unexpected id ~v" id))]))


(define (sprint-init cinit)
  (match cinit
    [#f ""]
    [(init:compound _ elements) (format "~a" (map sprint-compound elements))]
    [(init:expr _ expr) (sprint-cexp expr)]
    [(init src) ""]
    [_ (error "Unexpected initialization")]))

(define (sprint-inits inits)
  (format "~a" (map sprint-init inits)))


(define (sprint-qualifiers qualifiers)
  (string-join (map sprint-id qualifiers) " "))

; C statements 
(define (sprint-stmt stmt)
  (format 
   "~a"
   (match stmt
     [(stmt:label _ label stmt) (format "~a:\n~a" (sprint-id label)
                                        (indented (sprint-stmt stmt)))]
     [(stmt:case _ expr stmt) (format "case ~a:\n~a" (sprint-cexp expr) 
                                      (indented (sprint-stmt stmt)))]
     [(stmt:default _ stmt) (format "default:\n~a" (sprint-stmt stmt))]
     [(stmt:block _ items) (sprint-stmt-list items)]
     [(stmt:expr _ expr) (format "~a;\n" (sprint-cexp expr))]
     [(stmt:if _ test conss alt) (string-append 
                                  (format "if(~a) {\n~a}"
                                          (sprint-cexp test)
                                          (indented (sprint-stmt conss)))
                                  (match alt
                                    [#f "\n"]
                                    [_ (format " else {\n~a}\n"
                                               (indented (sprint-stmt alt)))]))]
     [(stmt:switch _ test body) (format "switch(~a) {\n~a}" 
                                        (sprint-cexp test)
                                        (indented (sprint-stmt body)))]
     [(stmt:while _ test body) (format "while(~a) {\n~a}"
                                       (sprint-cexp test)
                                       (indented (sprint-stmt body)))]
     [(stmt:do _ body test) (format "do {\n~a} while(~a);\n"
                                    (indented (sprint-stmt body))
                                    (sprint-cexp expr))]
     [(stmt:for _ ini test update body) (format "for(~a;~a;~a) {\n~a}\n"
                                                (sprint-cexp ini)
                                                (sprint-cexp test)
                                                (sprint-cexp update)
                                                (indented (sprint-stmt body)))]
     [(stmt:goto _ label) (format "goto ~a;\n" (sprint-id label))]
     [(stmt:break _) "break;\n"]
     [(stmt:continue _) "continue;\n"]
     [(stmt:return _ result) (format "return ~a;\n" (sprint-cexp result))]
     [(stmt:empty _) "skip;\n"]
     [ _ (error "Expected a statement but got something else ..")])))

(define (sprint-stmt-list stmt-list)
  (match stmt-list
    [(cons a b) (format "~a~a" 
                        (match a
                          [(stmt _) (sprint-stmt a)]
                          [(decl _) (sprint-decl a)])
                        (sprint-stmt-list b))]
    ['() ""]
    [a (sprint-stmt a)]))


(define (sprint-term term)
  "Not yet implemented : term printing")

(define (sprint-type ctype)
  (match ctype
    [(type:primitive _ name) (format "~a" name)]
    [(type:ref _ id) (sprint-id id)]
    [(type:struct _ tags fields) (format "struct ~a {\n~a}"
                                                (sprint-id tags)
                                                (indented (sprint-decl-list fields)))]
    [(type:union _ tags variants) (format "union ~a (~a)"
                                                 (sprint-id tags)
                                                 (sprint-decl-list variants))]
    [(type:enum _ tags variants) (format "enum ~a [~a]"
                                                 (sprint-id tags)
                                                 (sprint-decl-list variants))]
    [(type:array _ base static? qualifiers len star?) (format "~a~a~a[~a]"
                                                              (if (= static? #f)
                                                                  (sprint-id static?)
                                                                  "")
                                                              (sprint-qualifiers qualifiers)
                                                              (sprint-type base)
                                                              (sprint-cexp len)
                                                              )]
    [(type:pointer _ base qualifiers) (format "~a ~a*" (sprint-qualifiers qualifiers)
                                              (sprint-type base))]
    [(type:function _ return formals) (format "(~a)" 
                                              (sprint-formals formals))]
    [(type:qualified _ type qualifiers) (format "~a ~a" (sprint-type type)
                                                (sprint-qualifiers qualifiers))]
    [#f ""]
    [(type src) (format "Type:~a" (sprint-src src))]
    [_ (error "unexpected type for printing")]))

(define (sprint-src source)
  (match source
    [(src start-offset start-line start-col end-offset end-line end-col path)
     (format "~a:~a L ~a:~a C ~a:~a Path: ~a"
             start-offset end-offset start-line end-line
             start-col end-col path)]))


;; Pretty-printing utilities
(define default-indent 4)

(define (indented str)
  (let ([lines (string-split str "\n")])
    (string-join 
     (map 
      (lambda (s) (string-append (make-string default-indent #\space) s))
      lines)
     "\n"
     #:after-last "\n")))
