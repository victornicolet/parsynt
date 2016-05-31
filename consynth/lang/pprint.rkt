#lang racket

(require c
         racket/pretty)

; Printing C expressions
(define (sprint-cexp cexpr) 
  (parameterize 
      ([pretty-print-columns 80])
    (pretty-format 
     "~s"
     (match cexpr
       [(expr src) (format "Expression:~s" (sprint-src src))]
       [(expr:ref _ id) (sprint-id id)]
       [(expr:int _ val qualifiers) (format "~s ~s" val 
                                            (sprint-qualifiers qualifiers))]
       [(expr:float _ val qualifiers) (format "~s ~s" val 
                                              (sprint-qualifiers qualifiers))]
       [(expr:char _ source wide?) (format "char ~s" source)]
       [(expr:string _ source wide?) (format "string ~s" source)]
       [(expr:compound _ type inits) (format "~s ~s" (sprint-type type)
                                             (sprint-inits inits)) ]
       [(expr:array-ref _ expr offset) (format "~s[~s]"
                                               (sprint-cexp expr)
                                               (sprint-cexp offset))]
       [(expr:call _ func args) (format "~s (~s)"
                                        (sprint-cexp func)
                                        (sprint-cexp-list args))]
       [(expr:member _ expr label) (format "~s.~s" 
                                           (sprint-cexp expr)
                                           (sprint-id label))]
       [(expr:pointer-member _ expr label) (format "~s -> ~s"
                                                   (sprint-cexp expr)
                                                   (sprint-id label))]
       [(expr:postfix _ expr op) (format "~s ~s" (sprint-cexp expr) (sprint-id op))]
       [(expr:prefix _ op expr) (format "~s ~s" (sprint-id op) (sprint-cexp expr))]
       [(expr:cast _ type expr) (format "~s(~s)" (sprint-type type) (sprint-cexp expr))]
       [(expr:sizeof _ term) (format "sizeof(~s)" (sprint-term term))]
       [(expr:unop _ op expr) (format "~s ~s" (sprint-id op) (sprint-cexp expr))]
       [(expr:binop _ lexpr op rexpr) (format "~s ~s ~s"
                                             (sprint-cexp lexpr)
                                             (sprint-id op)
                                             (sprint-cexp rexpr))]
       [(expr:assign _ lexpr op rexpr) (format "~s ~s ~s"
                                               (sprint-cexp lexpr)
                                               (sprint-id op)
                                               (sprint-cexp rexpr))]
       [(expr:begin _ left right) (format "~s;\n~s"
                                          (sprint-cexp left)
                                          (sprint-cexp right))]
       [(expr:if _ test conss alt) (sprint-conditional test conss alt #f)]
       [_ ""]
))))




(define (sprint-cexp-list cexp-list)
  (match cexp-list
    [(cons a b) (format "~s, ~s" (sprint-cexp a) (sprint-cexp-list b))]
    ['() ""]
    [a (sprint-cexp a)]))

(define (sprint-compound element)
  (match element
    [(cons dtors ini) (pretty-format "~s ~s" 
                              (map sprint-designator dtor)
                              (sprint-init ini))]
    [ini (sprint-init ini)]))


(define (sprint-conditional test conss alt is-statement?)
  "Not yet implemented - COnditionals")

(define (sprint-decl cdecl)
  (match cdecl
    [(decl src) (format "Declaration:~s" (sprint-src src))]
    [(decl:typedef _ type declarators) (format "typedef ~s ~s;\n" 
                                               (sprint-type type)
                                               (map sprint-decl declarators))]
    [(decl:vars _ storage-class type declarators) (pretty-format 
                                                   "~s ~s ~s;\n"
                                                   (sprint-id storage-class)
                                                   (sprint-type type)
                                                   (map sprint-decl declarators))]
    [(decl:formal _ storage-class type declarator) (pretty-format
                                                   "~s ~s ~s"
                                                   (sprint-id storage-class)
                                                   (sprint-type type)
                                                   (sprint-decl declarator))]
    [(decl:function _ storage-class inline? return-type declarator preamble body)
     (pretty-format "~s~s ~s(~s) {\n~s}" 
                    (if inline? "inline " "") (sprint-id storage-class) 
                    (sprint-decl declarator) (sprint-decl-list preamble)
                    (sprint-stmt body))]
    [(decl:declarator _ id type initializer) (format "~s ~s~s"
                                                     (sprint-id id)
                                                     (sprint-type type)
                                                     (if (= initializer #f)
                                                         ""
                                                         (sprint-init initializer)))]
    [(decl:member-declarator _ id type initializer bit-size) (format "~s ~s~s [~s];\n"
                                                                     (sprint-id id)
                                                                     (sprint-type type)
                                                                     (sprint-init initializer)
                                                                     (sprint-cexp bit-size))]
    [(decl:member _ type declarators) (pretty-format "~s ~s\n"
                                                     (sprint-type type)
                                                     (map sprint-decl declarators))]))


(define (sprint-decl-list dlist)
  "Not yet implemented - list of declarations")

(define (sprint-designator designator)
  (match designator
    [(dtor src) ""]
    [(dtor:array _ expr) (format "[~s]" (sprint-cexp expr))]
    [(dtor:member _ label) (format ".~s" (sprint-id label))]))

;; (lsitof (or/c decl:formal? id:ellipsis?))
(define (sprint-formals formals) 
  "Not yet implemented yet")

(define (sprint-id id)
  (match id
    [(id:var _ name-symbol) (format "~s:~s" "var:" (symbol->string name-symbol))]
    [(id:label _ name-symbol) (format "~s:~s" "label:" (symbol->string name-symbol))]
    [(id:op _ name-symbol) (symbol->string name-symbol)]
    [(id:storage _ storage-class) (format "~s:~s" "class:" storage-class)]
    [(id:inline _) "inline"]
    [(id:qualifier _ name) (pretty-format "~s" name)]
    [_ "unrecognized id"]))


(define (sprint-init cinit)
  (match cinit
    [#f ""]
    [(init src) ""]
    [(init:compound _ elements) (pretty-format "~s" (map sprint-compound elements))]
    [(init:expr _ expr) (sprint-cexp expr)]))

(define (sprint-inits inits)
  (pretty-format "~s" (map sprint-init inits)))


(define (sprint-qualifiers qualifiers)
  (pretty-format "~s" (map sprint-id qualifiers)))

; C statements 
(define (sprint-stmt stmt)
  (parameterize
      ([pretty-print-columns 80])
    (pretty-format 
     "~s"
     (match stmt
       [(stmt:label _ label stmt) (format "~s ~s;\n" (sprint-id label) (sprint-stmt stmt))]
       [(stmt:case _ expr stmt) (format "case ~s:\n~s" (sprint-cexp expr) (sprint-stmt stmt))]
       [(stmt:default _ stmt) (format "default:\n~s" (sprint-stmt stmt))]
       [(stmt:block _ items) (sprint-stmt-list items)]
       [(stmt:expr _ expr) (format "~s\n" (sprint-cexp expr))]
       [(stmt:if _ test conss alt) (format "~s\n" (sprint-conditional test conss alt #t))]
       [(stmt:switch _ test body) (format "switch(~s) { \n~s}" 
                                          (sprint-cexp test)
                                          (sprint-stmt body))]
       [(stmt:while _ test body) (format "while(~s) {\n~s}"
                                         (sprint-cexp test)
                                         (sprint-stmt body))]
       [(stmt:do _ body test) (format "do {\n~s} while(~s)"
                                      (sprint-stmt body)
                                      (sprint-cexp expr))]
       [(stmt:for _ ini test update body) (format "for(~s;~s;~s) {\n~s"
                                                   (sprint-cexp ini)
                                                   (sprint-cexp test)
                                                   (sprint-cexp update)
                                                   (sprint-stmt body))]
       [(stmt:goto _ label) (format "goto ~s" (sprint-id label))]
       [(stmt:break _) "break;\n"]
       [(stmt:continue _) "continue;\n"]
       [(stmt:return _ result) (format "return ~s;\n" (sprint-cexp result))]
       [(stmt:empty _) "skip;\n"]))))

(define (sprint-stmt-list stmt-list)
  (match stmt-list
    [(cons a b) (format "~s\n~s;" (sprint-stmt a) (sprint-stmt-list b))]
    ['() ""]
    [a (sprint-stmt a)]))


(define (sprint-term term)
  "Not yet implemented : term printing")

(define (sprint-type ctype)
  (match ctype
    [(type src) (format "Type:~s" (sprint-src src))]
    [(type:primitive _ name) (pretty-format "~s" name)]
    [(type:ref _ id) (format "ref ~s" (sprint-id id))]
    [(type:struct _ tags fields) (pretty-format "struct ~s {~s}"
                                                (sprint-id tags)
                                                (sprint-decl-list fields))]
    [(type:union _ tags variants) (pretty-format "union ~s (~s)"
                                                 (sprint-id tags)
                                                 (sprint-decl-list variants))]
    [(type:enum _ tags variants) (pretty-format "enum ~s [~s]"
                                                 (sprint-id tags)
                                                 (sprint-decl-list variants))]
    [(type:array _ base static? qualifiers len star?) (format "~s~s~s[~s]"
                                                              (if (= static? #f)
                                                                  (sprint-id static?)
                                                                  "")
                                                              (sprint-qualifiers qualifiers)
                                                              (sprint-type base)
                                                              (sprint-cexp len)
                                                              )]
    [(type:pointer _ base qualifiers) (format "~s ~s*" (sprint-qualifiers qualifiers)
                                              (sprint-type base))]
    [(type:function _ return formals) (format "fun ~s -> ~s" 
                                              (sprint-formals formals)
                                              (sprint-type return))]
    [(type:qualified _ type qualifiers) (format "~s ~s" (sprint-type type)
                                                (sprint-qualifiers qualifiers))]))

(define (sprint-src source)
  (match source
    [(src start-offset start-line start-col end-offset end-line end-col path)
     (format "~s:~s L ~s:~s C ~s:~s Path: ~s"
             start-offset end-offset start-line end-line
             start-col end-col path)]))
