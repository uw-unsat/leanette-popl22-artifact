#lang rosette/safe

; all the routines for creating symbolic nonograms objects
; (basically, everything except programs)

(provide
  symbolic-segments
  symbolic-deduction
  symbolic-solution-segments/concrete-hints
  symbolic-line-transition
  symbolic-line
  solve-with-symbolic-deduction)

(require
  (only-in racket match-define error values parameterize hash-copy)
  rosette/lib/angelic
  "rules.rkt"
  "action.rkt"
  "../core/core.rkt")

(define (map/with-previous f lst)
  (reverse
    (foldl
      (λ (x acc)
        (define prev (if (empty? acc) #f (car acc)))
        (cons (f x prev) acc))
      empty
      lst)))

(define (make-list/with-previous len f)
  (reverse
    (foldl
      (λ (i acc)
        (define prev (if (empty? acc) #f (car acc)))
        (cons (f i prev) acc))
      empty
      (range/s 0 len))))

(define (symbolic-segments ctx max-segments)
  (define len (line-length ctx))
  (define-symbolic* num-segments integer?)
  (assert (>= num-segments 0))
  (assert (<= num-segments max-segments))
  (values
    (make-list/with-previous
      max-segments
      (λ (i prev)
        (define-symbolic* s integer?)
        (define-symbolic* e integer?)
        (define used? (< i num-segments))
        (assert (>= s 0))
        (assert (< s e))
        (assert (<= e len))
        (when prev
          ; must have gap of at least one between segments
          (assert (=> used? (> s (segment-end prev)))))
        (segment s e used?)))
    num-segments))

(define (symbolic-segments-of-lengths ctx lengths)
  (define len (line-length ctx))
  (map/with-previous
    (λ (x prev)
      (define-symbolic* s integer?)
      (define e (+ s x))
      (assert (>= s 0))
      (assert (<= e len))
      (when prev
        ; must have gap of at least one between segments
        (assert (> s (segment-end prev))))
      (segment s e #t))
    lengths))

; line? -> (listof segment?)
; create a set of symbolic solution segments for a concrete line,
; with assertions that the segments are consistent with a solution for that line.
; useful for either solving lines or generating solved lines.
(define (symbolic-solution-segments/concrete-hints ctx)
  (define hints (line-hints ctx))
  (define len (line-length ctx))
  (define segments
    ; use fold instead of map because we need to reference the previous segment
    (map/with-previous
      (λ (h prev)
        (define-symbolic* s integer?)
        (define e (+ s h))
        (assert (>= s 0))
        (assert (<= e len))
        (when prev
          ; must have gap of at least one between segments
          (assert (> s (segment-end prev))))
        (segment s e #t))
      hints))
  ; assert these segments are consistent with the board hints (will assert a solved line)
  (assert (segments-consistent? segments (line-cells ctx)))
  segments)

; line? -> line?
(define (symbolic-deduction start-ctx)
  (match-define (line hints cells) start-ctx)
  (line
    hints
    (map
      (λ (c) (if (empty-cell? c) (!!) c))
      cells)))

(define (symbolic-hint row-len)
  (define (symhint _)
    (define-symbolic* h integer?)
    (assert (> h 0))
    (assert (<= h row-len))
    h)
  (define max-hints (quotient (add1 row-len) 2))
  (build-list/s max-hints symhint))

; integer?, boolean? -> line-transition?
; line-transition-end will be a solved context (otherwise it's useless since the start might not be solvable).
; IMPORTANT NOTE: not all of the symoblics used to ensure solved? are part of the return value.
; So this should behave correctly in a verification context but not with e.g., quantifiers.
(define (symbolic-line-transition row-len)
  (define filled (map (λ (_) (!!* cell)) (range/s 0 row-len)))
  (define partial (map (λ (cell) (if (!!* known?) cell empty-cell)) filled))
  (define hnt (symbolic-hint row-len))
  (define num-hint (??* 0 (add1 (length hnt))))
  (define ctx (line (take hnt num-hint) partial))
  ; merely creating the symbolic segments creates the necessary asserts
  (symbolic-solution-segments/concrete-hints (line (line-hints ctx) filled))
  (line-transition ctx filled))

; creates a symbolic line.
; The line is provably consistent by actually generating a solved line and then emptying some cells.
; Thus, this is as expensive as a symbolic line-transition, and is just a convenience function.
; Much like symbolic-line-transition, the return value does not include all the symbolics created.
(define (symbolic-line row-len)
  (line-transition-start (symbolic-line-transition row-len)))

; f : (solver?, line?, (listof segment?) -> 'a)
; start-ctx: line?
; -> 'a
; creates a solver context which asserts the existence of a solved deduction from the given start context.
; then invokes the given procedure `f` with the solver, the solved line, and the segments for that line.
; returns whatever f returns.
(define (solve-with-symbolic-deduction f start-ctx)
  (with-terms
  (parameterize ([current-bitwidth #f])
    (define checker (current-solver))
    (solver-clear checker)
    (define end-ctx (eval-with-solver checker (symbolic-deduction start-ctx)))
    ; simply declaring this makes the asserts that end-ctx is correctly solved.
    (define segments (eval-with-solver checker (symbolic-solution-segments/concrete-hints end-ctx)))
    (f checker end-ctx segments))))
