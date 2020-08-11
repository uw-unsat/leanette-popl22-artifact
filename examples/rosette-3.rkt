#lang rosette

(define (abs x)
  (if (< x 0)
      (- x)
      x))

(define-symbolic y integer?)

(verify (assert (= (abs y) y)))
