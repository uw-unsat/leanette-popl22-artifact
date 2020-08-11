#lang racket

; routines to help create/view boards/lines/etc

(provide (all-defined-out))

(require
  "rules.rkt"
  "board.rkt"
  "action.rkt")

; string? -> state?
(define (string->cells s)
  (map
    (λ (c) (match c [#\- empty-cell] [#\x #f] [#\O #t] [#\? guessed-cell]))
    (string->list s)))

(define (cells->string s)
  (list->string
    (map
      (λ (c) (match c [#f #\x] [#t #\O] ['e #\?] [_ #\-]))
      s)))

; int list, string? -> line?
(define (make-line h s)
  (line h (string->cells s)))

; ... -> line-transition
(define (make-transition h s1 s2)
  (line-transition (make-line h s1) (string->cells s2)))

(define (make-line/fill h c v s e)
  (line/fill (make-line h c) (fill-action v s e)))

(define (pretty-format-line ctx)
  (format "(line ~a ~a)" (line-hints ctx) (cells->string (line-cells ctx))))

(define (pretty-format-transition tctx)
  (format "~a -> ~a" (pretty-format-line (line-transition-start tctx)) (pretty-format-line (line-transition-end tctx))))

; board? -> string?
; makes a pretty terminal rendering of a board. requires unicode terminal support.
(define (pretty-format-board brd)
  (match-define (board (spec row-hints col-hints) cells) brd)
  (define (pretty-format-state s)
    (string-join (map (λ (c) (if c "█" " ")) s) "" #:before-first "║" #:after-last "║"))
  ; HACK assumes all lines returns the rows first
  (define horz (make-string (length col-hints) #\═))
  (define middle (map (compose pretty-format-state line-cells) (take (board-all-lines brd) (length row-hints))))
  (define header (string-append "╔" horz "╗"))
  (define footer (string-append "╚" horz "╝"))
  (string-join (append (cons header middle) (list footer)) "\n"))

