#lang s-exp rosette

(require "network/network.rkt")
(require (except-in "juniper/config.rkt" as)) ; some people want to modify the loaded config

(define-namespace-anchor a)

(require "config.rkt")
(require "util/extraction-rosette.rkt")

(provide load-prop load-as load-driver
         denote-prop denote-import denote-export)

(define (load-prop args)
  (current-directory (car args))
  (define prop (list (file->string "setup.rkt") (cdr args)))
  (denote-prop prop)  ; only called to improve error reporting
  prop)

(define (load-as args)
  (current-directory (car args))
  (define ns (namespace-anchor->namespace a))
  ((parameterize ([current-namespace ns])
    (load "setup.rkt")
    (eval 'as)) (cdr args)))

(define (load-driver args)
  (current-directory (car args))
  (define ns (namespace-anchor->namespace a))
  (define driver ((parameterize ([current-namespace ns])
    (load "setup.rkt")
    (eval 'driver)) (cdr args)))
  driver)

(define denote-prop (lambdas (prop r i o p ai al al* ae) (begin
  (define setup (first prop))
  (define args (second prop))
  (define file (make-temporary-file))
  (define f (open-output-file file #:exists 'append))
  (write-string setup f)
  (close-output-port f)
  (define ns (namespace-anchor->namespace a))
  (define q ((parameterize ([current-namespace ns])
    (load file)
    (eval 'policy)) args))
  (if (q r i o p ai al al* ae) '(True) '(False)))))

(define denote-import (lambdas (as r i p a) (begin
  (match i
    ((Injected) `(NotAvailable))   ; TODO support static route configurations
    ((Received record)
      (match record ((ExistT record _)  ; connection
      (match record ((ExistT __ i*) (begin ; internal/external
        (define res (as-denote-import as r i* (announcement-prefix-set a p)))
        (if res `(Available ,res) `(NotAvailable))))))))))))

(define denote-export (lambdas (as r o p a) (begin
  (match o ((ExistT record _)  ; connection
    (match record ((ExistT __ o*) (begin ; internal/external
      (define res (as-denote-export as r o* (announcement-prefix-set a p)))
      (if res `(Available ,res) `(NotAvailable))))))))))
