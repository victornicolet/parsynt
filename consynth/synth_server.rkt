#lang racket

(require racket/sandbox
         rosette/safe)

(define server-name "localhost")
(define server-port 9877)
(define max-allow-wait 20); max concurrent clients waiting for turn
(define reuse? #f)
(define time-limit 120); secs for each rpc request
(define hostname #f) ; if #f any client accepted

(define (solve-sketch sketch)
  (with-handlers
    ([exn:fail? (lambda (e)
                  (exn-message e))])
    (eval sketch)))

(define (allowed? expr);; Filter out illegal requests here
  #t)

(define (exit-failure msg)
  (lambda (e) (eprintf "Failed : ~a" msg)))

(define (run-rpc-server)
  (define (accept-and-handle listener)
    (define cust (make-custodian))
    (custodian-limit-memory cust (* 50 1024 1024))
    (parameterize ((current-custodian cust))
      (define expr "")
      (define-values (client->me me->client) (tcp-accept listener))
      (define (handle)
        (set! expr (read client->me))
        (if (allowed? expr)
            (write (solve-sketch expr) me->client)
            (error "Illegal procedure call!" me->client)))
      (thread (lambda ()
                (handle)
                (close-output-port me->client)
                (close-input-port client->me))))
    (thread (lambda ()
              (sleep time-limit)
              (custodian-shutdown-all cust))))
  (define main-cust (make-custodian))
  (parameterize ((current-custodian main-cust))
    (define listener
      (with-handlers
        ([exn:fail:network?
          (lambda (e)
            ((eprintf "Connection to port ~a failed. Exiting ..." server-port)
             (exit 1)))]
         [exn:fail?
          (exit-failure "tcp-listen")])
        (tcp-listen server-port max-allow-wait reuse? hostname)))
    (define (loop)
      (accept-and-handle listener)
      (loop))
    (thread loop)
  (lambda ()
    (display "Exiting ...")
    (custodian-shutdown-all main-cust))))

(define stop (run-rpc-server))
