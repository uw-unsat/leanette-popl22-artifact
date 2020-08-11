#lang rosette

(require
  racket/runtime-path
  json
  "config.rkt"
  "core/core.rkt"
  "nonograms/nonograms.rkt"
  "learn/learning.rkt")

; XXX for profiling, hard-code the config path
(define-runtime-path toy.json "../config/toy.json")
(current-command-line-arguments (vector "-f" (path->string toy.json)))

(debug-print? #t)
(load-config 'batch)
(current-parallel-worker-count (config-ref 'num-workers))
(match-define (cons learning-cfg all-items) (deserialize-from-file (config-pathref 'work-list)))
(define batch-size (config-ref 'batch-size))
(define batch-outfile-prefix (config-ref 'outfile-prefix))

; integer? -> path?
(define (batch-outfile-name batch-index)
  (define orig (path->string (config-pathref 'learning-results)))
  (string->path (format "~a.~a.~a.batch" orig batch-outfile-prefix batch-index)))

(define start-time (current-seconds))

(printf "running rule learning on ~a items in batches of size ~a...\n" (length all-items) batch-size)
#|
(define (run-batch i work-items)
  (printf "running batch ~a\n" i)
  (define outfile (batch-outfile-name i))
  (subprocess-racket
    (list "src/run-single-batch.rkt")
    (λ (stdin)
      (write (serialize (list outfile learning-cfg work-items)) stdin)))
  ; have to return a list for run-batches, but we don't actually care about the result
  empty)
|#

(time
(for ([item all-items])
  (define items (list item))
  (define cfg learning-cfg)
  (define results (run-rule-learner-on-items cfg items))
  empty))

;(run-batches/parallel run-batch all-items #:batch-size batch-size)

(define end-time (current-seconds))
(print-time-delta start-time end-time)

