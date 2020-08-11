#lang racket

(require racket/runtime-path)
(require "../../src/bagpipe/racket/main/bagpipe.rkt")

(define-runtime-path root ".")

(time (verify (list (path->string root) "scenario4" "broken")))

(system "rm **/*.bak")
