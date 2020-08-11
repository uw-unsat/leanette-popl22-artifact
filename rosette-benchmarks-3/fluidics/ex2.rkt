#lang rosette

(require "lang.rkt")

(define (ex2)
 (synthesize-program
  (lambda (grid)
    (begin
      (grid-set! grid (point 0 0) 'a)
      (grid-set! grid (point 0 2) 'b)))
  (lambda (grid) (and (equal? 'a (grid-ref grid (point 4 2)))
                      (equal? 'b (grid-ref grid (point 0 0)))))))


(time (ex2))
