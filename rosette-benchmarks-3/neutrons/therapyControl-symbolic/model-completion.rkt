#lang racket

(require
  racket/hash
  (only-in rosette term-cache constant? model sat)
  (only-in rosette/base/core/type solvable-default get-type))

(provide complete)

; Returns a completion of the given solution that
; binds the provided constants to default concrete values.
; If no constants are provided, it uses the set of all constants
; that are present in the current term-cache.
(define complete
  (case-lambda
    [(sol)
     (complete sol (filter constant? (hash-values (term-cache))))]
    [(sol consts)
     (match sol
       [(model bindings)
        (sat
         (hash-union
          bindings
          (for/hash ([c consts] #:unless (dict-has-key? bindings c))
            (values c (solvable-default (get-type c))))))]
       [_ (error 'complete "expected a sat? solution, given ~a" sol)])]))
