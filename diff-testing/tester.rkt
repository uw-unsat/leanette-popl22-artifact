#lang racket

(provide main current-output current-timeout)
(require racket/cmdline
         "color.rkt"
         "metric.rkt")

(define DEFAULT-SEED 42)

(define current-verbose? (make-parameter #f))
(define current-rosette-verify? (make-parameter #f))
(define current-fuel
  (make-parameter
   "100"
   (λ (x)
     (unless (exact-nonnegative-integer? (string->number x))
       (raise-user-error
        "error: fuel must be an exact non-negative integer, got"
        x))
     x)))
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
(define current-mutation-depth
  (make-parameter
   5
   (λ (x)
     (unless (exact-nonnegative-integer? (string->number x))
       (raise-user-error
        "error: mutation-depth must be an exact non-negative integer, got"
        x))
     (string->number x))))
(define current-mutation-repeat
  (make-parameter
   10
   (λ (x)
     (unless (exact-nonnegative-integer? (string->number x))
       (raise-user-error
        "error: mutation-repeat must be an exact non-negative integer, got"
        x))
     (string->number x))))
(define current-mutators
  (make-parameter '()
                  (λ (x)
                    (append (match (file-or-directory-type x #t)
                              ['file (list x)]
                              ['directory (map ~a (directory-list x #:build? #t))])
                            (current-mutators)))))
(define current-timeout
  (make-parameter
   80
   (λ (x)
     (unless (exact-nonnegative-integer? (string->number x))
       (raise-user-error
        "error: timeout must be an exact non-negative integer, got"
        x))
     (string->number x))))
(define current-num-threads
  (make-parameter
   4
   (λ (x)
     (unless (exact-positive-integer? (string->number x))
       (raise-user-error
        "error: timeout must be an exact positive integer, got"
        x))
     (string->number x))))
(define current-output (make-parameter "workspace/log.rktd"))
(define current-mutation-ignore-error? (make-parameter #f))

(define rand-limit (expt 2 31))

(define (main progs)
  (with-output-to-file (current-output)
    #:exists 'replace
    void)

  (define *progs* progs)
  (define num-tasks (length *progs*))
  (define workers (make-hash))

  (for ([place-id (current-num-threads)])
    (define pch (dynamic-place "worker.rkt" 'place-main))
    (place-channel-put pch `(init ,place-id
                                  ,(modulo (+ (current-seed) num-tasks) rand-limit)
                                  ,(current-fuel)
                                  ,(current-rosette-verify?)
                                  ,(current-mutation-depth)
                                  ,(current-mutation-repeat)
                                  ,(current-mutation-ignore-error?)
                                  ,(current-mutators)
                                  ,(current-timeout)))
    (hash-set! workers place-id pch))

  (time
   (let loop ()
     (define all-workers (for/list ([(_ pch) (in-hash workers)]) pch))
     (match all-workers
       ['() (cprintf 'green "> finished all tasks\n")]
       [_
        (match (apply sync all-workers)
          [`(ready ,place-id)
           (define p (hash-ref workers place-id))
           (match *progs*
             ['() (place-kill p)
                  (hash-remove! workers place-id)]
             [(cons work next-progs)
              (cprintf 'magenta "Thread ~a is working, remaining tasks: ~a\n" place-id num-tasks)
              (set! num-tasks (sub1 num-tasks))
              (set! *progs* next-progs)
              (place-channel-put p `(work ,work))])]
          [`(ans ,prog ,lines)
           (define the-prog (dynamic-require prog 'expr))
           (define size (calc-size the-prog))
           (cprintf 'blue "======= Program ~a =======\n" prog)
           (define the-metric #f)
           (define the-rosette-metric #f)
           (define the-lean-metric #f)
           (define round 0)
           (define (reset)
             (set! the-metric (metric prog round size 'none 'none 'none))
             (set! round (add1 round))
             (set! the-rosette-metric (rosette-metric 'none 'none 'none))
             (set! the-lean-metric (lean-metric 'none 'none 'none)))
           (define (flush)
             (set-metric-lean! the-metric the-lean-metric)
             (set-metric-rosette! the-metric the-rosette-metric)
             (unless (current-rosette-verify?)
               (with-output-to-file (current-output)
                 #:exists 'append
                 (λ () (pretty-write the-metric)))))
           (reset)
           (for ([line lines])
             (match line
               ['flush
                (printf "Attempting to mutate...\n")
                (flush)
                (reset)]
               [`(verification-expectation ,ve)
                (printf "Expecting ~a\n" (match ve
                                           [#t "unsat"]
                                           [#f "model"]
                                           [_ "none, skipping"]))]
               [`(rosette-result ,r ,time)
                (set-rosette-metric-time! the-rosette-metric time)
                (printf "Computed in ~as\n" (~r (/ time 1000) #:precision 2))
                (displayln "Rosette*:")
                (displayln r)
                (displayln "")]
               [`(lean-result ,r ,time)
                (cond
                  [(equal? r "(none)")
                   (set! the-lean-metric 'out-of-fuel)
                   (set-metric-result! the-metric 'lean-out-of-fuel)
                   (cprintf 'red "Leanette runs out of fuel\n")]
                  [else
                   (set-lean-metric-time! the-lean-metric time)
                   (printf "Computed in ~as\n" (~r (/ time 1000) #:precision 2))
                   (displayln "Leanette:")
                   (displayln r)
                   (displayln "")])]
               ['verification-matched (cprintf 'green "Verification matched\n")]
               ['verification-unmatched (cprintf 'red "Verification unmatched\n")]
               [`(fatal-error ,s)
                (set! the-lean-metric 'fatal)
                (set-metric-result! the-metric 'lean-fatal-error)
                (cprintf 'red "Fatal error in Leanette compilation\n")
                (displayln "-------")
                (displayln s)
                (displayln "-------")]
               ['agree
                (set-metric-result! the-metric #t)
                (cprintf 'green "Leanette and Rosette* agree\n")]
               [`(disagree ,sol ,lean ,rosette)
                (set-metric-result! the-metric #f)
                (cprintf 'red "Leanette and Rosette* disagree\n")
                (displayln "Model:")
                (displayln sol)
                (displayln "Leanette's result:")
                (displayln lean)
                (displayln "Rosette*'s result:")
                (displayln rosette)]
               ['rosette-timeout
                (set! the-rosette-metric 'timeout)
                (set-metric-result! the-metric 'rosette-timeout)
                (cprintf 'red "Rosette* timeouts, likely encountering an infinite loop\n")]
               ['lean-timeout
                (set! the-lean-metric 'timeout)
                (set-metric-result! the-metric 'lean-timeout)
                (cprintf 'red "Leanette timeouts\n")]
               [`(lean-state ,trivial? ,stat)
                (when (lean-metric? the-lean-metric)
                  (set-lean-metric-size! the-lean-metric stat)
                  (set-lean-metric-trivial?! the-lean-metric trivial?))
                (printf "Leanette evaluation is ~a\n" (if trivial? "trivial" "non-trivial"))
                (printf "Leanette state size: ~a\n" stat)]
               [`(rosette-state ,trivial? ,stat)
                (set-rosette-metric-size! the-rosette-metric stat)
                (set-rosette-metric-trivial?! the-rosette-metric trivial?)
                (printf "Rosette* evaluation is ~a\n" (if trivial? "trivial" "non-trivial"))
                (printf "Rosette* state size: ~a\n" stat)]

               [`(lean-code ,lean-code)
                (when (current-verbose?)
                  (displayln "----- Leanette code -----")
                  (displayln lean-code))]
               [`(rosette-code ,rosette-code)
                (when (current-verbose?)
                  (displayln "----- Rosette* code -----")
                  (displayln rosette-code))]))])
        (loop)]))))

(module+ main
  (define progs
    (command-line
     #:once-each
     [("--rosette-verify") "Instead of doing differential testing, run the regular Rosette verification"
                           (current-rosette-verify? #t)]
     [("--fuel") f "Fuel used for Lean interpretation (default: 100)"
                 (current-fuel f)]
     [("--clean") "Instead of doing differential testing, clean all temporary files"
                  (for ([f (in-directory "workspace")])
                    (printf "Deleting ~a\n" f)
                    (delete-file f))
                  (exit 0)]
     [("--seed") s "Random seed. `-` means no seed. (default: 42)"
                 (current-seed s)]
     [("--mutation-depth") d "Mutation depth (default: 5)"
                           (current-mutation-depth d)]
     [("--mutation-repeat") n "Mutation repeat (default: 10)"
                            (current-mutation-repeat n)]
     [("--mutation-ignore-error") "Continue to mutate a program that doesn't pass differential testing"
                                  (current-mutation-ignore-error? #t)]

     [("--timeout") t "Timeout in seconds (default: 80)"
                    (current-timeout t)]
     [("--num-threads") n "Number of threads (default: 4)"
                        (current-num-threads n)]
     [("--out") o "Output path (default: workspace/log.rktd)"
                (current-output o)]
     [("--verbose") "Print Lean and Rosette code"
                    (current-verbose? #t)]
     #:multi
     [("--mutator") p "Mutator"
                    (current-mutators p)]
     #:args progs
     (filter
      (λ (p) (string-suffix? p ".rkt"))
      (append*
       (for/list ([prog progs])
         (match (file-or-directory-type prog #t)
           ['file (list prog)]
           ['directory (map ~a (directory-list prog #:build? #t))]))))))
  (main progs))
