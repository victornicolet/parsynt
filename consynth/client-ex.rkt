#lang racket
;XXX  CLIENT SIDE  XXX

(define server-name "localhost")
(define server-port 9877)

(define (rpc server-name expr); using default port
  (let-values (((server->me me->server)
                (tcp-connect server-name server-port)))
    (write expr me->server)-
    (close-output-port me->server)
    (let ((response (read server->me)))
      (close-input-port server->me)
      response)))

;XXX TEST RUN XXX

;; (run-rpc-server)

;; (rpc "localhost" '(+ 1 2 3))
;; (+ 5 (rpc "localhost" '(+ 1 2 3)) ); combine local with remote
