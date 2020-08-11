#lang racket

(provide (all-defined-out))
(require ansi-color)

(define (cprintf c fmt . rst)
  (with-colors c
    (λ () (color-display (apply format fmt rst)))))
