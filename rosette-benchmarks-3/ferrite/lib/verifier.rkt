#lang s-exp rosette

(require "fs.rkt" "lang.rkt" "litmus.rkt")

(provide (all-defined-out))

; Verify that a litmus test is valid. This checks that, for all valid
; reorderings of a program, and all crash-prefixes of that program, at
; least one of the allowed conditions in the litmus test holds.
; That is, it checks  ∀ trace. Valid(trace) ⇒ a_1 ∨ ⋯ ∨ a_n.
; @returns (values (solution? (or/c filesystem? #f))), where the solution is
;          sat? if there is a counterexample to the validity of the test.
;          If the solution is sat?, the second value is the state of the 
;          filesystem in that counterexample; otherwise it is #f.
(define (verify-correctness test)
  (clear-state!)
  (match-define (litmus make-fs setup prog allow) test)
  (define fs (make-fs))
  (when (> (length setup) 0)
    (set! setup (crack fs setup))
    (set! fs (interpret #:program setup
                        #:filesystem fs
                        #:crash? #f)))
  
  (set! prog (crack fs prog))
  (define-symbolic* order integer? [(length prog)])
  (define newfs (interpret #:program prog
                           #:filesystem fs
                           #:order order))

  (define allowed (allow fs newfs))

  (define allowed-cex
    (verify (assert (=> (valid-ordering fs prog order) (apply || allowed)))))

  (define cex-state (if (sat? allowed-cex) (evaluate newfs allowed-cex) #f))

  (values allowed-cex cex-state))
