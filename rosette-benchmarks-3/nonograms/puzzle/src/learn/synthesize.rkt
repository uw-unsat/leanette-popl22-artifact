#lang rosette/safe

(provide
  potential-program-exists?
  synthesize-program
  synthesize-program/no-generalization
  synthesize-program/inductive
  superoptimize-program
  sketch-covers?)

(require
  (only-in racket local-require)
  rosette/solver/smt/z3
  "cegis.rkt"
  "../core/core.rkt"
  "../nonograms/nonograms.rkt")

(define (consistent-with-bindings? ctx binding-prog binding-list)
  (define b (find-binding-for-pattern binding-prog ctx))
  (and
    b
    (&&map equal? b binding-list)))

; true iff the given binding determines the given output, and thus a program could exist
(define (potential-program-exists? tctx actn bnding)
  (parameterize-solver
    (define slvr (current-solver))
    (define ctx (line-transition-start tctx))
    (define end (line-transition-end tctx))
    ; create a symbolic context constrained to have the same concrete binding values as this transition.
    (define test-tctx (eval-with-solver slvr (symbolic-line-transition (line-length ctx))))
    (solver-assert* slvr (consistent-with-bindings? (line-transition-start test-tctx) bnding (find-binding-for-pattern bnding ctx)))
    ; rule exists if any context with these bindings can have this action applied to it.
    ; so try to find one that breaks it!
    (solver-assert* slvr (not (action-compatible-with-transition? actn test-tctx)))
    (define soln (solver-check slvr))
    (solver-clear slvr)

    (when (sat? soln)
      (printf "conflicting ctx: ~a\nbindings: ~a\n" (evaluate test-tctx soln) (find-binding-for-pattern bnding (line-transition-start (evaluate test-tctx soln)))))
    (when (unsat? soln)
      (printf "bindings: ~a\n" (find-binding-for-pattern bnding ctx)))

    (unsat? soln)))

; Implementation of the common bits of rule synthesis.
; Calls primary-guesser-assert-fn with the guess solver and program sktech
; so specific calls can enforce whatever existential constraints they want.
; This takes care of the CEGIS for rule soundness, plus some common extra
; exestential constrants such as forced-positive examples.
(define (synthesize-program-impl
          primary-guesser-assert-fn
          ; (listof int?)
          #:counter-example-parameters ce-parameters-seq
          ; whatever the parameters for a single sketch are
          #:sketch-parameters sketch-parameters
          #:objective-functions objective-functions-ctors
          #:program-eater eater
          #:counter-example-eater [eat-cex void]
          #:counter-example-functions [ce-func-ctors empty]
          #:optimization-state-update optimization-state-update
          )
  (parameterize-solver
    (define guesser (z3))
    (define verifiers (map create-verifier ce-parameters-seq))

    (solver-clear guesser)
    ; our program sketch
    (define sktch (eval-with-solver guesser (apply program-sketch sketch-parameters)))
    (define objective-functions (map (λ (f) (f guesser verifiers sktch)) objective-functions-ctors))
    ; symbolic assignment for finding counter-examples (no asserts)
    (define assn (map (λ (_) (??)) (Program-pattern sktch)))
    (define ce-funcs (map (λ (f) (f verifiers)) ce-func-ctors))

    (define (find-counter-example guess)
      (or
        ; if the programs behaves unsoundly
        (find-program-unsound-example verifiers guess assn)
        ; or if any objective function says there is a problem
        ; this is always "active" even if the OF has not started optimizing yet, they are expected to deal with this reasonably.
        ; (we want them to keep checking after they have reached their optimal, so it's just easier to leave them all on all the time).
        (ormap (λ (cefn) (cefn guess)) ce-funcs)
        (ormap (λ (of) ((synthesis-objective-function-find-counter-example of) guess)) objective-functions)))

    ; assert the primary exestential stuff
    (primary-guesser-assert-fn guesser sktch)

    (define (synthesize)
      (run-cegis guesser sktch #:find-counter-example find-counter-example #:eater eater #:eat-counter-example eat-cex))

    (define result
      (run-incremental-optimization
        guesser
        synthesize
        objective-functions
        #:notification-function optimization-state-update))

    (solver-shutdown guesser)
    (for-each verifier-shutdown verifiers)
    result))

; Program?, line-transition? -> boolean?
; Returns true iff the given program applies to and effects a non-trivial action on the given line transition.
; Either may be symbolic.
(define (positive-example? program tctx assn)
  (define ctx (line-transition-start tctx))
  (define action (interpret/nondeterministic program (create-environment ctx) #:binding-assignments assn))
  (and action (action-compatible-with-and-impactful-for-transition? action tctx)))

(define (negative-example? program tctx assn)
  (define ctx (line-transition-start tctx))
  (define action (interpret/nondeterministic program (create-environment ctx) #:binding-assignments assn))
  (not action))

(define (create-higher-generalization-optimization generalization-set-parameters)
  (λ (guesser verifiers sktch)
    ; can use same set of symbolic transitions the entire time because each better program engulfs the previous,
    ; so one transition should be new for every previous program
    (define transitions (eval-with-solver guesser (map symbolic-line-transition generalization-set-parameters)))
    ; symbolic assignment for finding counter-examples (this makes no assertions)
    (define assn (map (λ (_) (??)) (Program-pattern sktch)))
    ; either empty (at start) or the singleton list of the best program so far, used for cex finding
    (define programs-to-generalize empty)
    (synthesis-objective-function
      'generalization
      (λ (prog)
        (dprintf "trying to increase generalization")
        (set! programs-to-generalize (list prog))
        ; assert that at least one of these transitions is covered by the sktch that is not covered by the found program
        (solver-assert* guesser
          (lormap
            (λ (tctx)
              (define assn (map (λ (_) (??)) (Program-pattern sktch)))
              (&& (positive-example? sktch tctx assn) (negative-example? prog tctx assn)))
            transitions)))
      (λ (guess)
        ; if there exists some input covered by a program we must generalize but not this one
        (find-program-uncovered-example verifiers guess programs-to-generalize assn)))))

(define (create-lower-cost-optimization)
  (λ (guesser _ sktch)
    (synthesis-objective-function
      'cost
      (λ (prog)
        (define c (program-cost prog))
        (dprintf "trying to lower cost below ~a" c)
        (solver-assert* guesser (< (program-cost sktch) c)))
      (λ (_) #f))))

(define (synthesize-program
          #:input ctx
          #:output actn
          #:binding bnding
          #:counter-example-parameters ce-params
          #:generalization-set-parameters gs-params
          #:program-eater [eater void]
          #:optimization-state-update [optimization-state-update void]
          )
  (define (assertfn guesser sktch)
    (solver-assert* guesser
      (equal?
        (interpret/nondeterministic sktch (create-environment ctx))
        actn)))
  (define objectives
    (list
      (create-higher-generalization-optimization gs-params)
      (create-lower-cost-optimization)))
  (synthesize-program-impl
     assertfn
     #:counter-example-parameters ce-params
     ; TODO XXX ignoring features for now
     #:sketch-parameters (list empty ctx bnding)
     #:program-eater eater
     #:optimization-state-update optimization-state-update
     #:objective-functions objectives))

(define (synthesize-program/no-generalization
          #:input ctx
          #:output actn
          #:binding bnding
          #:counter-example-parameters ce-params
          #:program-eater [eater void]
          #:optimization-state-update [optimization-state-update void]
          #:debug-force-use-program [forced-program #f]
          )
  (define (assertfn guesser sktch)
    (when forced-program
      (solver-assert* guesser (equal? sktch forced-program)))
    (solver-assert* guesser
      (equal?
        (interpret/nondeterministic sktch (create-environment ctx))
        actn)))
  (define objectives
    (list
      (create-lower-cost-optimization)))
  (synthesize-program-impl
     assertfn
     #:counter-example-parameters ce-params
     ; TODO XXX ignoring features for now
     #:sketch-parameters (list empty ctx bnding)
     #:program-eater eater
     #:optimization-state-update optimization-state-update
     #:objective-functions objectives))

(define (synthesize-program/inductive
          ; (listof (pairof line? line-action?))
          #:input io-examples
          #:pattern pat
          #:counter-example-parameters ce-params
          #:program-eater [eater void])
  (local-require (only-in racket for))
  (define (assertfn guesser sktch)
    (for ([pr io-examples])
      (solver-assert* guesser
        (equal?
          (interpret/nondeterministic sktch (create-environment (car pr)))
          (cdr pr)))))
  (define objectives
    (list
      (create-lower-cost-optimization)))
  (synthesize-program-impl
     assertfn
     #:counter-example-parameters ce-params
     ; TODO XXX ignoring features for now
     #:sketch-parameters (list empty (car (first io-examples)) pat)
     #:program-eater eater
     #:optimization-state-update void
     #:objective-functions objectives))

; finds the lowest-cost program that covers all the same programs as the given program while using the same bindings.
; Also behaves exactly the same on primary-input, returning the primary output
(define (superoptimize-program
          #:primary-input ctx
          #:primary-output actn
          #:program prog
          #:counter-example-parameters ce-params
          #:program-eater eater)
  (define (assertfn guesser sktch)
    (solver-assert* guesser
      (< (program-cost sktch) (program-cost prog)))
    (solver-assert* guesser
      (equal?
        (interpret/nondeterministic sktch (create-environment ctx))
        actn)))
  (define objectives
    (list
      (create-lower-cost-optimization)))
  (define cefuncs
    (list
      (λ (verifiers)
        (define assn (map (λ (_) (??)) (Program-pattern prog)))
        (λ (guess)
          ; if there exists some input covered by a program we must generalize but not this one
          (find-program-uncovered-example verifiers guess (list prog) assn)))))
  (synthesize-program-impl
     assertfn
     #:counter-example-parameters ce-params
     ; TODO XXX ignoring features for now
     #:sketch-parameters (list empty #f (Program-pattern prog))
     #:program-eater eater
     #:counter-example-functions cefuncs
     #:optimization-state-update void
     #:objective-functions objectives))

(define (sketch-covers? prog sketch-parameters)
  (parameterize-solver
    (define sktch (program-sketch sketch-parameters #f (Program-pattern prog)))
    (define-syntax-rule (check f) (sat? (solve (assert (equal? (f sktch) (f prog))))))
    ;(displayln
    ;  (list
    ;    (check Program-pattern)
    ;    ;(check (compose first Program-pattern))
    ;    ;(check (compose second Program-pattern))
    ;    ;(check (compose third Program-pattern))
    ;    (check Program-condition)
    ;    (check (compose Fill-offset Program-action))
    ;    (check (compose Fill-start Program-action))
    ;    (check (compose Fill-end Program-action))
    ;    ));(check Program-action)))
    (sat? (solve (assert (equal? sktch prog))))))

