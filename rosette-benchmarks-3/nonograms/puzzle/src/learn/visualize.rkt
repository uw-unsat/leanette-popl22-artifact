#lang racket

(provide (all-defined-out))

(require
  "../core/core.rkt"
  "../learn/optimization.rkt"
  "../nonograms/nonograms.rkt"
  "../nonograms/builtin.rkt"
  "../nonograms/dsl-pretty.rkt"
  "../nonograms/debug.rkt")

; result visualization code

; (listof optimization-item?) -> xexpr?
(define (create-analysis-visualization result-items)
  (define (format-result i item)
    (define score (optimization-item-score item))
    (define r (optimization-item-program item))
    (define prog
      (program->stylized-html (apply-all-rewrite-rules r) (format "prog~a" i)))
    (xexp div
      (h3 ,(format "Result ~a" i))
      (p ,(format "Score: ~a" score))
      (p "Program:")
      (div ,prog)))

  (xexp html
    ,visualization-html-header
    (body
      (h2 "Optimal Rules")
      ,@(mapi format-result result-items))))

