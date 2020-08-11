#lang racket

(provide
 run-with-timeout
 run-with-timeout/eater)

; integer? (seconds), 'a, () -> 'a, string? -> 'a
; Executes func with a time limit of timeout seconds.
; If func returns, within that time, returns that value.
; Otherwise, if (procedure? timeout-val) returns the result of executing timeout-val with no arguments.
; Otherwise, returns timeout-val.
; This functions creates a new custodian and terminates it when finished.
(define (run-with-timeout timeout timeout-val func #:timeout-message [timeout-msg ""])
  (define cust (make-custodian))
  (define alarm (alarm-evt (+ (current-inexact-milliseconds) (* timeout 1000))))
  (define T
    (parameterize ([current-custodian cust])
      (thread
        (thunk
          (flush-output)
          (define result-thread (thread-receive))
          (flush-output)
          (define val (func))
          (thread-send result-thread val)))))
  (thread-send T (current-thread))
  (define tre (thread-receive-evt))
  (match (sync/timeout timeout tre)
   [(== tre) ; our result
    (define val (thread-receive))
    (custodian-shutdown-all cust)
    val]
   [#f
    (custodian-shutdown-all cust)
    (displayln (format "Timeout ~a" timeout-msg))
    (if (procedure? timeout-val) (timeout-val) timeout-val)]))

; Same as run-with-timeout, except func is passed an eater procedure.
; If timeout is reached, will return the most recent value passed to eater,
; or timeout-val if nothing has been passed to the eater.
(define (run-with-timeout/eater timeout timeout-val func #:timeout-message [timeout-msg ""])
  (define tv (box timeout-val))
  (define (eat x) (set-box! tv x))
  (define (get) (unbox tv))
  (run-with-timeout timeout get (thunk (func eat)) #:timeout-message timeout-msg))

