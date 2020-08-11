#lang racket

; this is really only a separate file because places need a non-main file

(provide
  enumerate-maximal-transitions
  find-strongest-transitions)

(require
  rosette/solver/smt/z3
  (only-in rosette solver-shutdown current-solver)
  "../core/core.rkt"
  "../nonograms/nonograms.rkt")

; cells? -> line?
; computes the hints for a given fully-specified row, returning as a line?
(define (hints-from-row row)
  (define (foldfn x acc)
   (match-define (cons lst prev) acc)
   (cond
    [x (if prev (cons lst (add1 prev)) (cons lst 1))]
    [else (if prev (cons (cons prev lst) #f) acc)]))
  (define hnt (reverse (car (foldl foldfn (cons '() #f) (append row (list #f))))))
  (line hnt row))

; integer? -> state? list
; all possible 2^len nonogram rows of length len.
(define (all-full-rows len)
  (cond
   [(<= len 0) (raise-argument-error 'len "positive-integer?" len)]
   [(= len 1) '((#f) (#t))]
   [else
    (define rst (all-full-rows (sub1 len)))
    (append
      (map (curry cons '#f) rst)
      (map (curry cons '#t) rst))]))

; line? -> line? list
; given a fully specified line, computes all 2^n partial lines.
(define (all-partials ctx)
  (match-define (line hnt row) ctx)
  (define (rec row)
    (match row
     ['() (raise-argument-error 'ctx "line? with non-empty row" ctx)]
     [(list x)
      (list row (list empty-cell))]
     [(cons head tail)
      (define rst (rec tail))
      (append
        (map (curry cons head) rst)
        (map (curry cons empty-cell) rst))]))
  (map (λ (r) (line hnt r)) (rec row)))

(define (all-lines-of-size n)
  (append-map all-partials (map hints-from-row (all-full-rows n))))

(define (enumerate-init-fn index data)
  (z3))

(define (enumerate-terminate-fn index checker)
  (solver-shutdown checker))

(define (enumerate-work-fn checker ctx)
  (parameterize ([current-solver checker])
    (define tctx (strongest-deduction-of ctx))
    (and (line-transition-productive? tctx)
         (line-transition-has-minimal-start? tctx)
         tctx)))

; int? -> (listof line-transition?)
; Returns all maximal (least start, greatest end) transitions for lines of length line-len.
(define (enumerate-maximal-transitions line-len #:canonical-only? [canonical-only? #t])
  (dprintf "enumerating maximal transitions of length ~a (out of ~a possible contexts)" line-len (expt 4 line-len))
  (define all-ctx (remove-duplicates (all-lines-of-size line-len)))
  (define to-use
    (if canonical-only?
        (parallel-map/place
          #:initialize enumerate-init-fn
          #:map enumerate-work-fn
          #:finalize enumerate-terminate-fn
          #:list all-ctx)
        all-ctx))
  (filter-map identity to-use))

(define (deduction-work-fn checker ctx)
  (parameterize ([current-solver checker])
    (strongest-deduction-of ctx)))

(define (find-strongest-transitions start-contexts)
  (parallel-map/place
    #:initialize enumerate-init-fn
    #:map deduction-work-fn
    #:finalize enumerate-terminate-fn
    #:list start-contexts))

