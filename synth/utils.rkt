#lang rosette/safe


(provide PolytopeLU get-synthax
)
;; Generates the assertions for a polytope P such that each  a < u and a <=
;; (PolytopeLU [lower bounds ..] [indexes ... ] [upper bounds ...])
(define-syntax PolytopeLU
  (syntax-rules ()
    [(PolytopeLU [l ...] [a ...] [u ...]) 
     (assert (and (and (< a u) (<= l a)) ...)) ]))

(define (get-synthax synthesis-solution) 
  (car synthesis-solution))
