#lang racket

(provide (all-defined-out))

(require
  json)

(define (write-to-file fname obj)
  (call-with-output-file fname #:exists 'truncate (λ (out) (write obj out))))

(define (read-from-file fname)
  (call-with-input-file fname (λ (in) (read in))))

(define (write-to-string val)
  (define port (open-output-string))
  (write val port)
  (get-output-string port))

(define (read-from-string str)
  (define port (open-input-string str))
  (read port))

(define (write-blank-file fname)
  (call-with-output-file fname #:exists 'truncate (λ (out) (void))))

(define (write-full-json fname obj)
  (call-with-output-file fname #:exists 'truncate (λ (out) (write-json obj out))))

(define (read-json-file fname)
  (call-with-input-file fname (λ (in) (read-json in))))

(define (write-append-json fname obj)
  (call-with-output-file fname #:exists 'append (λ (out) (write-json obj out) (displayln "" out))))

(define (format-csv elems)
  (define (to-str e)
    (if (string? e)
        e
        (format "~v" e)))

  (string-join (map to-str elems) ","))

(define (write-full-csv fname headers lines)
  (call-with-output-file
    fname
    #:exists 'truncate
    (λ (out)
      (displayln (format-csv headers) out)
      (for ([line lines])
        (displayln (format-csv line) out)))))

(define (start-csv fname headers)
  (call-with-output-file
    fname
    #:exists 'truncate
    (λ (out)
      (displayln (format-csv headers) out))))

(define (add-csv-line fname line)
  (call-with-output-file
    fname
    #:exists 'append
    (λ (out)
      (displayln (format-csv line) out))))

(define-syntax-rule (collect-time eater body ...)
  (let ()
    (define-values (vlst cpu real gc) (time-apply (λ (_) body ...) (list 0)))
    (eater real)
    (first vlst)))

(define-syntax-rule (collect-time-into-hash (hm key) body ...)
  (collect-time (λ (x) (hash-set! hm key x)) body ...))

