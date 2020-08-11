#lang rosette

(require
  "util.rkt"
  "lift.rkt"
  rosette/solver/smt/z3
  rosette/base/core/type
  rosette/lib/angelic)

(provide
 choose
 symbolic?
 ??
 ??*
 !!
 !!*
 ignore-asserts
 eval-with-solver
 solver-assert*
 solver-assert-not*
 assert*
 list-sketch
 option-map
 arbitrary-concretization
 parameterize-solver
 parameterize-solver-bw
 with-asserts)

(define-syntax-rule (with-asserts e)
  (let* ([r (with-vc e)]
         [v (result-value r)]
         [s (result-state r)])
    (values v (list (vc-assumes s) (vc-asserts s)))))

(define (choose . lsts)
  (apply choose* (apply append lsts)))

(define (symbolic? x)
  (not (empty? (symbolics x))))

(define (??)
  (define-symbolic* c integer?)
  c)

(define (??* s e)
  (define-symbolic* c integer?)
  (assert (>= c s))
  (assert (< c e))
  c)

(define (!!)
  (define-symbolic* b boolean?) 
  b)

(define-syntax-rule (!!* name)
  (let ()
    (define-symbolic* name boolean?)
    name))

(define-syntax-rule (ignore-asserts s)
  (let-values ([(r _) (with-asserts s)])
    r))

(define-syntax-rule (eval-with-solver slvr expr)
  (let-values ([(e asrts) (with-asserts expr)])
    (solver-assert slvr asrts)
    e))

(define-syntax-rule (solver-assert* slvr expr)
  (let-values ([(e asrts) (with-asserts expr)])
    (solver-assert slvr (cons e asrts))))

(define-syntax-rule (solver-assert-not* slvr expr)
  (let-values ([(e asrts) (with-asserts expr)])
    (solver-assert slvr (list (ormap not (cons e asrts))))))

; assert without throwing
(define-syntax-rule (assert* expr)
  (assert expr (thunk (void))))

(define (list-sketch f max-len [min-len 0])
  (define-symbolic* len integer?)
  (assert (>= len min-len))
  (assert (<= len max-len))
  (take (build-list/s max-len (λ (_) (f))) len))

(define-syntax-rule (option-orelse to-try or-else)
  (let ([result to-try])
    (if result result or-else)))

(define (option-map to-do result)
  (if result (to-do result) #f))

(define (arbitrary-concretization x)
  (evaluate
    x
    (sat
      (for/hash ([s (symbolics x)])
        (values s (solvable-default (type-of s)))))))

(define-syntax-rule (parameterize-solver-bw bw stmt ...)
  (with-terms
    (parameterize ([current-solver (z3)]
                   [current-bitwidth bw])
      (define x (let () stmt ...))
      (solver-shutdown (current-solver))
      (clear-vc!)
      x)))

(define-syntax-rule (parameterize-solver stmt ...)
  (parameterize-solver-bw #f stmt ...))
