#lang rosette/safe

(provide (all-defined-out))

(require
  (only-in racket match-define hasheq)
  rosette/lib/match
  "../core/core.rkt")

; a single row/column of a board, both hints and state
; hints: (listof integer?), cells: (listof boolean?)
(standard-struct line (hints cells))
; a segment is a location for a contiguous run of filled cells, definied by a start and end.
; the solver works by creating one symbolic segment for each hint of the appropriate length,
; guessing the starting index of the segment, and ensuring all segments are consistent with
; the board's symbolic cells.
; When generating, rather than generate a symbolic number of segments, we generate the maximum
; number of possible segments and then symbolically enable some of them. The used? field
; implements this concept. Segments only matter if used? is true.
; start: integer?, end: integer?, used?: boolean.
(standard-struct segment (start end used?))
(define (segment-size g) (- (segment-end g) (segment-start g)))

(define (line->json ctx)
  (match-define (line h s) ctx)
  (hasheq 'start (map (λ (c) (if (empty-cell? c) 'null c)) s)
          'hints h))

; line? -> integer?
(define (line-length ctx) (length (line-cells ctx)))

(define empty-cell 'e)
(define true-cell #t)
(define false-cell #f)
(define (empty-cell? c) (equal? c empty-cell))
(define (true-cell? c) (equal? c #t))
(define (false-cell? c) (equal? c #f))
; Strict defintion of cell. Must be empty/true/false.
(define (cell? c) (or (empty-cell? c) (true-cell? c) (false-cell? c)))
; Extended cells, which can also contain guesses. Used only for visualization
(define guessed-cell 'g)
(define (guessed-cell? c) (equal? c guessed-cell))
(define (cell-ex? c) (or (cell? c) (guessed-cell? c)))

(define (line-filled? ctx)
  (not (ormap empty-cell? (line-cells ctx))))

; line? -> boolean?
(define (line-solved? ctx)
  (match-define (line hints cells) ctx)
  (define (check-next cell acc)
    (cond
     [acc
      (define hints-remaining (car acc))
      (define current-count (cdr acc))
      (cond
       ; if no more hints, cell better be false
       [(empty? hints-remaining)
        (and (not cell) acc)]
       ; if the cell is empty then it's not correct
       [(empty-cell? cell) #f]
       [(true-cell? cell)
        (cons hints-remaining (add1 current-count))]
       ; otherwise if false, check if we matched the hints
       [(= current-count (first hints-remaining))
        (cons (rest hints-remaining) 0)]
       [else
        (and (= current-count 0) acc)])]
     [else #f]))
  (define res (foldl check-next (cons hints 0) (append cells (list #f))))
  (and res (empty? (car res))))

; segment?, (listof boolean?) -> boolean?
; returns true if the given set of segments is consistent with the given line of cells.
; if segments are consistent with a set of hints, this is equivalent to checking if the line is solved.
(define (segments-consistent? segments cells)
  (&&mapi
    (λ (i c)
      (equal? c (lormap (λ (s) (&& (segment-used? s) (<= (segment-start s) i) (< i (segment-end s)))) segments)))
    cells))

; (segment-subset? a b) is true iff a's range is a subrange of b (and both are the same used?)
(define (segment-subset? to-check other)
  (&& (<=> (segment-used? to-check) (segment-used? other))
      (<= (segment-start other) (segment-start to-check))
      (>= (segment-end other) (segment-end to-check))))

; returns true is to-check is <= to other according to the partial ordering of lines based on information.
; Line a <= b if b can be reached from a by filling in empty cells.
(define (line-weaker? to-check other)
  (match-define (line hint-a row-a) to-check)
  (match-define (line hint-b row-b) other)
  (and
    (equal? hint-a hint-b)
    (= (length row-a) (length row-b))
    (andmap
      (λ (tc oth) (or (empty-cell? tc) (equal? tc oth)))
      row-a
      row-b)))

