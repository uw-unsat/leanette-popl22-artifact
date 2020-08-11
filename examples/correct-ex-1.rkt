#lang rosette

(define (abs x)
  (if (< x 0)
      (- x)
      x))

(define-symbolic y integer?)

(verify
 (begin
   (assume (not (= y 0)))
   (assert (> (abs y) 0))))
