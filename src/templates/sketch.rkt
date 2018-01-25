(define-symbolic a integer?)
(define (f x) ((choose + - / *) 1 x))
(define odot (synthesize  #:forall (list a) #:guarantee (= (f a) a)))
