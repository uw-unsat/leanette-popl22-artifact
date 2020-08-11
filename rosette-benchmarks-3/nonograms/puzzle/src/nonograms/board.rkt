#lang rosette

(provide (all-defined-out))

(require
  rosette/lib/match
  "../core/core.rkt"
  "rules.rkt")

; board spec, the hints for all rows and columns
; row-hints: (listof (listof integer?)), col-hints: (listof (listof integer?))
(standard-struct spec (row-hints col-hints))
; a board, spec + array of cells, row major
; spec: spec?, cells: (vectorof boolean?)
(standard-struct board (spec cells))
; type: (choiceof 'row 'col)
; index: integer?
; line: line?
(standard-struct board-line (type index line))

(define (copy-board brd)
  (struct-copy board brd [cells (vector-copy (board-cells brd))]))

(define (board-width brd)
  (length (spec-col-hints (board-spec brd))))

(define (board-height brd)
  (length (spec-row-hints (board-spec brd))))

; board?, integer?, integer? -> boolean?
; references a cell at the given column x and row y
(define (board-ref brd x y)
  (define width (board-width brd))
  (vector-ref (board-cells brd) (+ (* width y) x)))

(define (board-set! brd x y c)
  (define width (length (spec-col-hints (board-spec brd))))
  (vector-set! (board-cells brd) (+ (* width y) x) c))

; board? -> (listof line?)
; every line of a given board
(define (board-all-lines brd)
  (match-define (board (spec row-hints col-hints) cells) brd)
  (define width (length col-hints))
  (define height (length row-hints))
  (append
    (for/list ([y height]
               [h row-hints])
      (line h (for/list ([x width]) (board-ref brd x y))))
    (for/list ([x width]
               [h col-hints])
      (line h (for/list ([y height]) (board-ref brd x y))))))

(define (board-solved? brd)
  (andmap line-solved? (board-all-lines brd)))

; board? -> (listof board-line?)
; all rows of the given board
(define (board-rows brd)
  (define width (board-width brd))
  (define height (board-height brd))
  (for/list ([y (board-height brd)]
             [h (spec-row-hints (board-spec brd))])
    (board-line 'row y (line h (for/list ([x width]) (board-ref brd x y))))))

; board? -> (listof board-line?)
; all columns of the given board
(define (board-cols brd)
  (define width (board-width brd))
  (define height (board-height brd))
  (for/list ([x (board-width brd)]
             [h (spec-col-hints (board-spec brd))])
    (board-line 'col x (line h (for/list ([y height]) (board-ref brd x y))))))

(define (board-lines-of-type typ brd)
  (match typ
   ['row (board-rows brd)]
   ['col (board-cols brd)]))

(define (board-line-infos brd)
  (append
    (board-rows brd)
    (board-cols brd)))

; board?, board-line? -> void?
(define (board-set-line! brd bl)
  (match-define (board (spec row-hints col-hints) cells) brd)
  (match-define (board-line typ idx (line _ lc)) bl)
  (define width (length col-hints))
  (define (bset! x y c)
    (vector-set! cells (+ (* width y) x) c))
  (match typ
   ['row
    (for ([x width]
          [c lc])
      (bset! x idx c))]
   ['col
    (for ([y (length row-hints)]
          [c lc])
      (bset! idx y c))]))

; int list list, int list list -> board?
(define (make-empty-board row-hints col-hints)
  (define w (length col-hints))
  (define h (length row-hints))
  (board (spec row-hints col-hints) (make-vector (* w h) empty-cell)))

(define (json->board jval)
  (define hints (hash-ref jval 'hints))
  (define rows (hash-ref hints 'rows))
  (define cols (hash-ref hints 'cols))
  (make-empty-board rows cols))

