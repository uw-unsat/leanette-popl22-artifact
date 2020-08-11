#lang racket

(provide define-series format-rosette-code choose)
(require syntax/parse/define
         racket/splicing
         (for-syntax racket/list))

(define-syntax-parse-rule (define-series [x:id ...] e:expr)
  #:with (padder ...) (range (length (attribute x)))
  (splicing-let ([e* e])
    (define x (+ (#%datum . padder) e*))
    ...))

(define (format-rosette-code rosette-code)
  (string-join (cons "#lang rosette\n"
                     (map (curry pretty-format #:mode 'write) rosette-code))
               "\n"))

(define (choose xs)
  (list-ref xs (random (length xs))))
