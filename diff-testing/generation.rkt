#lang racket

(require data/enumerate/lib
         racket/cmdline
         math
         "utils.rkt")

(define DEFAULT-SEED 42)

(define current-max-bool-vars
  (make-parameter
   5
   (λ (x)
     (unless (exact-positive-integer? (string->number x))
       (raise-user-error
        "error: max-bool-vars must be an exact positive integer, got"
        x))
     (string->number x))))

(define current-max-int-vars
  (make-parameter
   5
   (λ (x)
     (unless (exact-positive-integer? (string->number x))
       (raise-user-error
        "error: max-int-vars must be an exact positive integer, got"
        x))
     (string->number x))))

(define current-max-iterations
  (make-parameter
   500
   (λ (x)
     (unless (exact-positive-integer? (string->number x))
       (raise-user-error
        "error: iterations must be an exact positive integer, got"
        x))
     (string->number x))))

(define current-max-sub-iterations
  (make-parameter
   20
   (λ (x)
     (unless (exact-positive-integer? (string->number x))
       (raise-user-error
        "error: sub-iterations must be an exact positive integer, got"
        x))
     (string->number x))))

(define current-seed
  (make-parameter
   DEFAULT-SEED
   (λ (x)
     (match x
       ["-" #f]
       [_
        (unless (exact-nonnegative-integer? (string->number x))
          (raise-user-error
           "error: seed must be an exact non-negative integer or `-`, got"
           x))
        (string->number x)]))))

(define current-int-scope
  (make-parameter
   2
   (λ (x)
     (unless (exact-nonnegative-integer? (string->number x))
       (raise-user-error
        "error: int-scope must be an exact non-negative integer, got"
        x))
     (string->number x))))

(command-line
 #:once-each
 [("--max-bool-vars") v "Number of max bool variables (default: 5)"
                      (current-max-bool-vars v)]
 [("--max-int-vars") v "Number of max int variables (default: 5)"
                      (current-max-int-vars v)]
 [("--iterations") lv "Number of iterations (default: 500)"
                   (current-max-iterations lv)]
 [("--sub-iterations") lv "Number of sub-iterations (default: 20)"
                       (current-max-sub-iterations lv)]
 [("--seed") s "Random seed. `-` means no seed. (default: 42)"
             (current-seed s)]
 [("--int-scope") n "Integer scope (default: 2)"
                  (current-int-scope n)])

(when (current-seed)
  (random-seed (current-seed)))

(define var/e (range/e 0 (sub1 (+ (current-max-bool-vars)
                                  (current-max-int-vars)))))

(define integer-range/e (range/e (- (current-int-scope)) (add1 (current-int-scope))))

(define expr/e
  (delay/e
   (or/e
    (list/e (single/e 'var) var/e)
    (list/e (single/e 'let0) var/e expr/e expr/e)
    (list/e (single/e 'λ) var/e expr/e)
    (list/e (single/e 'if0) var/e expr/e expr/e)
    (list/e (single/e 'make-error))
    (list/e (single/e 'make-abort))
    (list/e (single/e 'app) (fin/e '+ '* '< '= 'link) var/e var/e)
    (list/e (single/e 'app) (fin/e 'first 'rest 'null?) var/e)
    (list/e (single/e 'app) (single/e 'make-null))
    (list/e (single/e 'call) var/e var/e)
    (list/e (single/e 'datum) (list/e (single/e 'op.lang.datum.int) integer-range/e))
    bool/e)))

(define seen (mutable-set))

(define (gen-init-env)
  (shuffle (append (make-list (current-max-bool-vars) 'bool)
                   (make-list (current-max-int-vars) 'int))))

(define (generate i)
  (cond
    [(set-member? seen i)
     (define low (add1 i))
     (define high (* 2 (add1 i)))
     (generate (random low high))]
    [else
     (printf "Generating index ~a\n" i)
     (set-add! seen i)
     (define rosette-code
       `((provide expr env verification-expectation)
         (define expr ',(from-nat expr/e i))
         (define env ',(gen-init-env))
         (define verification-expectation 'none)))
     (with-output-to-file (~a "generation/prog" i ".rkt")
       #:exists 'replace
       (λ () (displayln (format-rosette-code rosette-code))))]))

(for ([i (current-max-sub-iterations)])
  (generate i))

;; skip 0
(for ([i (in-range 1 (current-max-iterations))])
  (for ([j (current-max-sub-iterations)])
    (generate (random-natural (expt 2 i)))))
