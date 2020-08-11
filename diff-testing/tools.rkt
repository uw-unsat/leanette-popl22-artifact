#lang racket

(provide debug:)

(define (debug: . xs)
  (pretty-print xs)
  (last xs))
