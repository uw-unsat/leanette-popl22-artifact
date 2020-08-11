#lang racket
(require rosette)
(require "env.rkt")
(provide explain-counterexample)

; returns a string with some text explaining the counterexample
(define (explain-counterexample cex)
  (let [(m (model cex))]
    (foldl string-append "" (map (lambda (k) (explain1 m k)) (hash-keys m)))))

(define (ppval v)
  (cond
    [(bv? v) (format "~a [~a-bit]" (bitvector->integer v) (bitvector-size (type-of v)))]
    [(boolean? v) (if v "true" "false")]
    [#t (format "~s" v)]))

(define (explain1 m v)
  (format "~a = ~a\n" (symb-name v) (ppval (hash-ref m v))))
