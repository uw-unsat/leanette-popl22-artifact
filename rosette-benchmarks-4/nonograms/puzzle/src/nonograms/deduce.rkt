#lang rosette

; routines related to using the solver to make deductions about lines/boards.

(provide (all-defined-out))

(require
  rosette/solver/smt/z3
  "../core/core.rkt"
  "rules.rkt"
  "action.rkt"
  "context.rkt"
  "board.rkt"
  "symbolic.rkt")
         

; line? -> line-transition?
; calculates the largest possible transition logically deducible from the given line line,
; using the solver as an oracle.
(define (strongest-deduction-of start-ctx)
   ; greedily check every cell to see if they can be set
  (with-terms
  (parameterize ([current-bitwidth #f])
    (define checker (current-solver))
    (define-values (end-ctx end-ctx-asserts) (with-asserts (symbolic-deduction start-ctx)))
    (define-values (segments seg-asserts) (with-asserts (symbolic-solution-segments/concrete-hints end-ctx)))

    ; first get a sanity solution to ensure it's even solvable
    (solver-clear checker)
    (solver-assert checker end-ctx-asserts)
    (solver-assert checker seg-asserts)
    (define sanity-soln (solver-check checker))

    (define r
      (cond
       [(sat? sanity-soln)
        (define state0 (line-cells (evaluate end-ctx sanity-soln)))
        (define state1 (line-cells end-ctx))
        ; then, for each empty cell in start-ctx, check if there is another solution that differs on that cell.
        (define (test i)
          (define o (list-ref (line-cells start-ctx) i))
          (cond
           [(empty-cell? o)
            (define c (list-ref state0 i))
            (solver-push checker)
            (solver-assert* checker (not (equal? c (list-ref state1 i))))
            (define soln (solver-check checker))
            (solver-pop checker)
            (if (unsat? soln) c o)]
           [else o]))
        (define dctn (map test (range/s 0 (length state0))))
        (line-transition start-ctx dctn)]
       [else #f]))
    r)))

; returns #t if the given line transition is minimal in the following sense:
; there does not exist any line strictly weaker than start-line
; from which end-line is deducible.
; That is, start-line is (locally) the weakest assumptions necessary to reach end-line.
(define (line-transition-has-minimal-start? dctx)
  (define start (line-transition-start dctx))
  (define end (line-transition-end dctx))
  (andmap
    (λ (i)
      (define other (line-set-cell start i empty-cell))
      (or
        (equal? other start)
        (not (line-weaker? end (line-transition-end (strongest-deduction-of other))))))
    (range/s 0 (length (line-cells start)))))

; true iff the line-transition's start and end states are not equal
(define (line-transition-productive? dctx)
  (define start (line-transition-start dctx))
  (define end (line-transition-end-cells dctx))
  (not (equal? (line-cells start) end)))

; board? -> board?
; Solves a board using the SMT solver.
(define (solve-board brd)
  (parameterize-solver
    (define symbrd (struct-copy board brd [cells (vector-map (λ (_) (!!)) (board-cells brd))]))
    (define all-lines (board-all-lines symbrd))
    (for-each symbolic-solution-segments/concrete-hints all-lines)
    (define soln (solve (assert #t)))
    (and (sat? soln) (evaluate symbrd soln))))

