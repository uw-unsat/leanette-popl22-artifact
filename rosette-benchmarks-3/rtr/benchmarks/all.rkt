#lang racket

(require (only-in rosette/safe clear-state! current-solver)
         rosette/solver/smt/cvc4
         syntax/parse/define
         syntax/location)

#;(pretty-display
 (for/list ([x (in-directory ".")] #:when (and (string-suffix? (~a x) ".rkt")
                                               (not (equal? "./all.rkt" (~a x)))))
   (~s (~a x))))

(define-for-syntax all-inputs
  '("./RubyMoney/translated0.rkt"
    "./RubyMoney/translated1.rkt"
    "./RubyMoney/translated2.rkt"
    "./RubyMoney/translated3.rkt"
    "./RubyMoney/translated4.rkt"
    "./RubyMoney/translated5.rkt"
    "./RubyMoney/translated6.rkt"
    "./boxroom/translated.rkt"
    "./business_time/translated0.rkt"
    "./business_time/translated1.rkt"
    "./business_time/translated2.rkt"
    "./business_time/translated3.rkt"
    "./business_time/translated4.rkt"
    "./business_time/translated5.rkt"
    "./business_time/translated6.rkt"
    "./business_time/translated7.rkt"
    "./business_time/translated8.rkt"
    "./business_time/translated9.rkt"
    "./geokit/translated0.rkt"
    "./geokit/translated1.rkt"
    "./geokit/translated2.rkt"
    "./geokit/translated3.rkt"
    "./geokit/translated4.rkt"
    "./geokit/translated5.rkt"
    "./matrix/translated0.rkt"
    "./unitwise/translated0.rkt"
    "./unitwise/translated1.rkt"
    "./unitwise/translated2.rkt"
    "./unitwise/translated3.rkt"
    "./unitwise/translated4.rkt"
    "./unitwise/translated5.rkt"))

(define-syntax-parser run-all-tests
  [(_)
   #:with (mod-id ...) (generate-temporaries all-inputs)
   #:with (mod-path ...) (generate-temporaries all-inputs)
   #:with (path ...) all-inputs
   (syntax/loc this-syntax
     (begin
       (begin
         (module mod-id racket
           (require path))
         (current-solver (cvc4))
         (define mod-path (quote-module-path mod-id))
         (dynamic-require mod-path #f)
         (clear-state!)) ...))])

(define-syntax-parse-rule (require-all-tests)
  #:with (path ...) all-inputs
  (begin (require path) ...))

(run-all-tests)

(module+ line-count
  (require-all-tests))
