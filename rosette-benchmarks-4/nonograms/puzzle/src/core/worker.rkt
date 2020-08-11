#lang racket

(provide (except-out (all-defined-out) slice))

(require
  "parallel.rkt"
  "serialize.rkt")

(define (slice lst start end)
  (take (drop lst start) (- end start)))

(define (racket-executable)
  (define path (find-system-path 'exec-file))
  (cond
   ; If find-system-path returns the rather useless "racket" (which is does on my linux box),
   ; use the shell to find whatever racket is on the path and assume it's the correct one.
   [(string=? (path->string path) "racket")
    (string->path (string-trim (with-output-to-string (thunk (system "which racket")))))]
   [else path]))

; path?, (output-port? -> void?) -> void?
; Execute the racket program at `script-path` with `args` CLI arguments,
; using `(stdin-write-proc <new-stdin>)` for stdin.
; Blocks until the subprocess exits.
(define (subprocess-racket args stdin-write-proc #:read-stdout? [read-stdout? #f])
  ; if current-output-port is not a file port, have to reroute it through another port
  (define-values (proc stdout stdin stderr)
    (apply
      subprocess
      (append
        (list
          (and (not read-stdout?) (current-output-port))
          #f
          (current-error-port)
          (racket-executable))
        args)))
  (stdin-write-proc stdin)
  (close-output-port stdin)
  (subprocess-wait proc)
  (cond
   [read-stdout?
    (define rv (read stdout))
    (close-input-port stdout)
    rv]
   [else
    (void)]))

(define (run-in-subprocess args in-data)
  (deserialize
    (subprocess-racket args (λ (p) (write (serialize in-data) p)) #:read-stdout? #t)))

(define (evaluate-in-subprocess module-path expr stdin-data)
  (run-in-subprocess (list "-l" "racket/base" "-t" module-path "-e" expr) stdin-data))

; invoke f on batches of lst of at most batch-size, using parallel-map/thread.
(define (run-batches/parallel f lst #:batch-size batch-size)
  (define item-count (length lst))
  (define batches
    (for/list ([i (range 0 (ceiling (/ item-count batch-size)))])
      (define start (* i batch-size))
      (cons i (slice lst start (min (+ start batch-size) item-count)))))
  (apply append (parallel-map/thread (λ (pr) (f (car pr) (cdr pr))) batches)))

; runs f on sublists of lst of at most size batch-size, sequentially, and appends all results
(define (run-batches/sequential f lst #:batch-size batch-size)
  (define item-count (length lst))
  (append-map
    (λ (i)
      (define start (* i batch-size))
      (define elems (slice lst start (min (+ start batch-size) item-count)))
      (f i elems))
    (range 0 (ceiling (/ item-count batch-size)))))

