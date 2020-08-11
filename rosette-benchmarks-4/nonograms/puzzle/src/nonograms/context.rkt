#lang racket

; line (e.g., line, board) manipulation routines
; that are not core to the rules and mechanics.

(provide
  update-line-cells
  line-set-cell
  transition->fills
  transition->deltas
  flip-line
  flip-action
  flip-delta
  merge-symmetric-deltas
  line-transition-rank
 )

(require
  "../core/core.rkt"
  "rules.rkt"
  "action.rkt")

(define (update-line-cells f ctx)
  (match-define (line hints cells) ctx)
  (line hints (mapi f cells)))

(define (line-set-cell ctx idx val)
  (define (set-cell i c) (if (= i idx) val c))
  (update-line-cells set-cell ctx))

; line-transition -> line-fill list
; Separates a transition into actions that maximally fill each contiguous block changed by the transition.
(define (transition->fills tctx)
  (define start (line-cells (line-transition-start tctx)))
  (define finish (line-transition-end-cells tctx))

  ; boolean? if changed, empty-cell if not
  (define cells
    (map
      (λ (s e) (if (equal? s e) empty-cell e))
      start finish))

  (define (run-of val idx cnt)
    ; we're going backwards (foldr), so the run started at the "next" value
    (fill-action val (add1 idx) (+ 1 idx cnt)))

  (define (loop idx x acc)
    (match-define (list res val cnt) acc)
    (cond
     [(equal? val x)
      (list res val (add1 cnt))]
     [(boolean? val)
      (list (cons (run-of val idx cnt) res) x 1)]
     [else
      (list res x 1)]))
  ; fold over the runs to build up the list, the actual results is the first element of the accumulator
  (define acc (foldr loop (list empty empty-cell 0) (range (length start)) cells))
  (match-define (list res val cnt) acc)
  (if (boolean? val)
      (cons (run-of val -1 cnt) res)
      res))

; same as transition->fills, only returns a list of line/fill? instead of fill-action?
(define (transition->deltas tctx)
  (map (curry line/fill (line-transition-start tctx)) (transition->fills tctx)))

; flips a line by reversing the state and the hints
(define (flip-line ctx)
  (match-define (line h s) ctx)
  (line (reverse h) (reverse s)))

(define (flip-action line-len actn)
  (match-define (fill-action val start end) actn)
  (fill-action val (- line-len end) (- line-len start)))

(define (flip-delta dctx)
  (match-define (line/fill ctx actn) dctx)
  (define line-len (length (line-cells ctx)))
  (line/fill (flip-line ctx) (flip-action line-len actn)))

; line-delta? list -> line-delta list list
; groups all deltas that are symmetric.
; assuming a list with no repeats that is overall symmetric,
; elements of returned list with either have 2 or 1 entries depending on if each delta is self-symmetric.
(define (merge-symmetric-deltas deltas)
  ; hooray for naive n^2 algorithms
  ; this is fast enough as long as we use vectors instead of lists.
  (define dvec (list->vector deltas))
  (define len (vector-length dvec))
  (for*/list ([i (in-range len)]
              [flipped (list (flip-delta (vector-ref dvec i)))]
              [j (in-range i len)]
              #:when (equal? (vector-ref dvec j) flipped))
    (remove-duplicates (list (vector-ref dvec i) flipped))))

; heuristic sorting function for line transitions to view the "simple" ones first
(define (line-transition-rank tctx)
  (match-define (line-transition (line hint start) finish) tctx)
  ; thinks that lower the rank:
  ;   low number of hints
  ;   large difference between start and finish
  (length hint))

#|

; how many empty cells are set by a delta
(define (line-delta-impact dctx)
  (match-define (line-transition (line _ s) e) (line-delta->transition dctx))
  (count (λ (c1 c2) (not (equal? c1 c2))) s e))

; how many empty cells are set by a transition
(define (line-transition-impact tctx)
  (match-define (line-transition (line _ s) e) tctx)
  (count (λ (c1 c2) (not (equal? c1 c2))) s e))

(define (board-line* brd key)
  (board-line brd (car key) (cdr key)))

(define (board-all-line-keys brd)
  (define-values (width height) (board-dim brd))
  (append
    (build-list height (curry cons 'row))
    (build-list width (curry cons 'col))))

; board?, line-key?, action? -> void?
(define (board-apply-action! brd ckey action)
  (match-define (fill-action val start end) action)
  (match ckey
   [(cons 'row y)
    (for ([x (in-range start end)])
      (board-set! brd x y val))]
   [(cons 'col x)
    (for ([y (in-range start end)])
      (board-set! brd x y val))]))

(define (board-apply-transition! brd ckey tctx)
  (define cells (line-transition-end-state tctx))
  (match ckey
   [(cons 'row y)
    (for ([x (in-range (board-width brd))]
          [c cells])
      (board-set! brd x y c))]
   [(cons 'col x)
    (for ([y (in-range (board-height brd))]
          [c cells])
      (board-set! brd x y c))]))

; line-transition -> line-action list
|#

