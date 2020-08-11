#lang racket

(require racket/path)

(current-command-line-arguments (vector "verify" "." "scenario3" "broken"))

(define module-path "/root/bagpipe/src/bagpipe/racket/main/bagpipe.rkt")
(define resolved (find-relative-path (current-directory) module-path #:more-than-root? #t))

(time
(dynamic-require `(submod ,resolved main) #f))