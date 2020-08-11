#lang rosette/safe

(provide
  (struct-out counter-example)
  create-verifier
  verifier-shutdown
  verify-program
  use-verifiers
  find-program-unsound-example
  find-program-uncovered-example
  run-cegis
  (struct-out synthesis-objective-function)
  run-incremental-optimization)

(require
  (only-in racket match-define for hash-count exit)
  rosette/lib/match
  rosette/lib/angelic
  rosette/solver/smt/z3
  "../core/core.rkt"
  "../nonograms/nonograms.rkt"
  "../nonograms/dsl-pretty.rkt")

; the generic (ish) parts of the CEGIS routine, without all the extra bells and whistles (mainly the optimizations).

; definitely don't want to be serializing this thing
(struct verifier (solver transition environment) #:transparent)

; an input that breaks a particular program
; input: line?
; bindings: (listof integer?) the indices for each non-deterministic binding in the counter example.
(standard-struct counter-example (input bindings type))

; also definitely do not want to serialize this
; name : symbol? - name of this objctive
; do-assert: Program? -> void? - given last valid guess, assert (on the guesser) constraints to improve this objective
; find-counter-example: Program? -> (or/c false? counter-example?) return any counter examples that decrease this objective
; By convention, all OFs should be constructed with the following signature:
; solver?, (listof? verifier?), (and/c Program? symbolic?) -> synthesis-objective-function?
(struct synthesis-objective-function (name do-assert find-counter-example) #:transparent)

(define (verifier-shutdown vfr)
  (solver-shutdown (verifier-solver vfr)))

(define (create-verifier ce-params)
  (define checker (z3))
  (define tctx (eval-with-solver checker (symbolic-line-transition ce-params)))
  (define env (eval-with-solver checker (create-environment (line-transition-start tctx))))
  (verifier checker tctx env))

(define-syntax-rule (use-verifiers ([verifiers ce-parameters-seq]) stmt ...)
  (parameterize-solver
    (define verifiers (map create-verifier ce-parameters-seq))
    (define res (let () stmt ...))
    (for-each verifier-shutdown verifiers)
    res))

; (listof verifier?), Program?, (listof? int?) -> (or/c false? counter-example?)
; returns an input (if it exists) for whih this program is unsound (violates the domain rules)
(define (find-program-unsound-example vfrs prog assn)
  (define (unsound-example? env tctx)
    ; unsound example allowed to demonically choose the nondeterministic binding assignments
    (define r (interpret/nondeterministic prog env #:binding-assignments assn))
    (and r (not (action-compatible-with-transition? r tctx))))
  (define (test vfr)
    (match vfr
     [(verifier checker tctx env)
      (solver-push checker)
      (solver-assert* checker (unsound-example? env tctx))
      (define soln (solver-check checker))
      (solver-pop checker)
      ;(when (sat? soln) (printf "~v\n" (arbitrary-concretization (evaluate (list tctx segs env) soln))))
      (and (sat? soln) (arbitrary-concretization (evaluate (counter-example tctx assn 'unsound) soln)))]))
  (ormap test vfrs))

; (listof verifier?), Program?, (listof Program?) (listof? int?) -> (or/c false? counter-example?)
; returns an input (if it exists) for which the condition holds for some program in comparison-progs but not prog
(define (find-program-uncovered-example vfrs prog comparison-progs assn)
  (define (uncovered-example? oldprog env tctx)
    ; assumes the programs have "similar" bindings
    ; this is true if we're trying to learn a generalization
    (define rold (interpret/nondeterministic oldprog env #:binding-assignments assn))
    (define rnew (interpret/nondeterministic prog env #:binding-assignments assn))
    (and rold (not rnew)))
  (define (test oldprog vfr)
    (match vfr
     [(verifier checker tctx env)
      (solver-push checker)
      (solver-assert* checker (uncovered-example? oldprog env tctx))
      (define soln (solver-check checker))
      (solver-pop checker)
      ;(when (sat? soln) (printf "~v\n" (arbitrary-concretization (evaluate (list tctx segs env) soln))))
      (and (sat? soln) (arbitrary-concretization (evaluate (counter-example tctx assn 'uncovered) soln)))]))
  (ormap (λ (p) (ormap (curry test p) vfrs)) comparison-progs))

; Program?, (listof integer?) -> (or/c false? line-transition?)
(define (verify-program
          prog
          #:counter-example-parameters ce-parameters-seq)
  (use-verifiers ([verifiers ce-parameters-seq])
    (define assn (map (λ (_) (??)) (Program-pattern prog)))
    (find-program-unsound-example verifiers prog assn)))

; Program?, (and/c counter-example? concrete?) -> boolean?
; True if the program is okay for the given counter example.
(define (good-example? program counter-ex)
  (match counter-ex
   [(counter-example tctx assn 'unsound)
    (define ctx (line-transition-start tctx))
    (define result (interpret/nondeterministic/concrete-env program (create-environment ctx) #:binding-assignments assn))
    (or
      (not result)
      (action-compatible-with-transition? result tctx))]
   [(counter-example tctx assn 'uncovered)
    (define ctx (line-transition-start tctx))
    (define result (interpret/nondeterministic/concrete-env program (create-environment ctx) #:binding-assignments assn))
    (not (not result))]))


; solver?, Program?, (Program? -> counter-example?), (Program? -> void?), (counter-example? -> void?) -> (or/c false? Program?)
; run the CEGIS routine, given a routine for finding counter examples.
; Returns either a program with no counter examples or #f.
; `eater` is invoked with the return value, if found.
; `eat-cex` is invoked for each counter-example? found.
(define (run-cegis guesser sktch #:find-counter-example find-counter-example #:eater eater #:eat-counter-example eat-cex)
  (let synthesize ()
    (define soln (solver-check guesser))
    (cond
     [(sat? soln)
      (define guess (arbitrary-concretization (evaluate sktch soln)))
      (dprintf "guess: ~a" (debug-format-program guess))
      (define counter-ex (arbitrary-concretization (find-counter-example guess)))
      (cond
       [counter-ex
        (dprintf "ce: ~v" counter-ex)
        (eat-cex counter-ex)
        (solver-assert* guesser (good-example? sktch counter-ex))
        (synthesize)]
       [else
        (dprintf "synthesized valid!")
        (eater guess)
        guess])]
     [else
      (dprintf "failed!")
      #f])))

; (void?->'a|#f), ('a->void?) -> 'a|#f
(define (run-incremental-optimization-impl slvr notifyfn guessfn objctv initial-guess)
  (notifyfn `(optimization-started ,objctv))
  (define (rec last-guess)
    (solver-push slvr)
    ((synthesis-objective-function-do-assert objctv) last-guess)
    (define guess (guessfn))
    (cond
     [guess
      (rec guess)]
     [else
      (notifyfn `(optimization-finished ,objctv))
      (solver-pop slvr)
       last-guess]))
  (and initial-guess (rec initial-guess)))

(define (run-incremental-optimization slvr guessfn objectives #:notification-function [notifyfn void])
  (define (rec lst last-guess)
    (match lst
     [(cons head tail)
      (rec tail (run-incremental-optimization-impl slvr notifyfn guessfn head last-guess))]
     ['() last-guess]))
  (rec objectives (guessfn)))


