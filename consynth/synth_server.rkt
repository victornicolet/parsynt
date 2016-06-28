#lang racket

(require racket/sandbox
         rosette/lib/synthax
         rosette/safe)

(define server-name "localhost")
(define server-port 9877)
(define max-allow-wait 20); max concurrent clients waiting for turn
(define reuse? #f)
(define time-limit 120); secs for each rpc request
(define hostname #f) ; if #f any client accepted

(define user-home (find-system-path 'home-dir))

(define-values (rst_par rst mbdir?) (split-path (collection-path "rosette")))
(define z3solver (build-path rst_par (string->path "bin/z3")))

(define (init-file file-output-port)
  (fprintf file-output-port  "(require rosette rosette/lib/synthax)~n")
  (flush-output file-output-port))

(define (finish-file file-output-port solution-pathname)
  (fprintf file-output-port "(define forms (car (generate-forms odot)))~n")
  (fprintf file-output-port
           "(define solution-out (open-output-file ~s #:exists 'truncate))~n \
  (write (syntax->datum forms) solution-out)~n \
  (close-output-port solution-out)~n" (path->string solution-pathname)))


(define rosette-evaluator
  (parameterize
      ([sandbox-path-permissions (list (list 'execute z3solver))])
    (make-evaluator 'rosette)))

(define (rosette-eval sk)
  (define odot (rosette-evaluator sk))
  (print-forms odot)
  (flush-output)
  odot)

(define (solve-sketch sketch)
  ;; We need to save the sketch to a file, otherwise rosette will not be
  ;; able to return a solution. Here we use the system's temprorary files
  ;; directory : files will not be saved or reused after Rosette's solution
  ;; as been sent to the client.
  (define tempFilePath (make-temporary-file "rosettetmp~a" #f #f))
  (define solFilePath (make-temporary-file "rosetteSolTmp~a" #f #f) )
  ;; Save the sketch received from the client to the temp file
  (define tempFileOut (open-output-file tempFilePath #:exists 'truncate))
  (init-file tempFileOut)
  (fprintf tempFileOut "~a" (syntax->datum sketch))
  (finish-file tempFileOut solFilePath)
  (close-output-port tempFileOut)

  ;; REMOVE THIS -- !!!!!!!!
  (copy-file tempFilePath (build-path user-home "000tempFileOut.txt"))
  (with-handlers
    ([exn:fail? (lambda (e)
                  (exn-message e))])
    (load tempFilePath))
  (define solInput (open-input-file solFilePath))
  (define sol (read solInput))
  (close-input-port solInput)
  (copy-file solFilePath (build-path user-home "000solFile.txt"))
  (with-handlers
    ([exn:fail:filesystem?
      (lambda (e)
        (eprintf "Couldn't delete temp file.\nError : ~a"
                 (exn-message e)))])
    (delete-file tempFilePath)
    (delete-file solFilePath))
  sol)

(define (allowed? expr) #t)

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
        (set! expr (read-syntax "tcp-input" client->me))
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
            ((eprintf "~a\n" (exn-message e))
             (eprintf "Connection to port ~a failed. Exiting ..." server-port)
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
