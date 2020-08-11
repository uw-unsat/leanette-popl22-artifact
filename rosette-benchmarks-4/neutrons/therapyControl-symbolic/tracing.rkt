#lang rosette
(provide (all-defined-out))

(struct StartProcessing (record-name) #:transparent)
(struct EndProcessing (record-name) #:transparent)
(struct SkipProcessing (record-name) #:transparent)
(struct WriteField (record-name field-name value) #:transparent)

(define trace (list))

(define (record-trace msg)
  (set! trace (append trace (list msg))))

(define (reset-trace)
  (set! trace (list)))

(define (get-trace) trace)
