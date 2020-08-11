#lang racket

(provide
  visualize-row
  visualize-board
  visualization-html-header)

(require
  "rules.rkt"
  "board.rkt"
  #;"../core/xml.rkt")

;; HACK by james
(define-syntax-rule (xexp . rest) #f)

; cell-ex? -> xexpr?
(define (cell->xexpr cell)
  (cond
   [(empty-cell? cell)
    (xexp td #:class "cell")]
   [else
    (define classes
      (cond
       [(true-cell? cell)
        "fa fa-stop yes"]
       [(false-cell? cell)
        "fa fa-close no"]
       [(guessed-cell? cell)
        "fa fa-square-o guess"]))
    (xexp td #:class "cell" (i #:class ,classes))]))

(define (hint->xexpr h)
  (xexp span ,h))

; line? -> xexpr?
(define (row->xexpr ln)
  (define hints (let ([h (line-hints ln)]) (if (empty? h) '(0) h)))
  (xexp tr
    (th #:class "hint row" ,@(map hint->xexpr hints))
    ,@(map cell->xexpr (line-cells ln))))

; line? -> xexpr?
(define (visualize-row ln)
  (xexp table ,(row->xexpr ln)))

(define (colhints->xexpr hints)
  (xexp th #:class "hint col" ,@(map hint->xexpr hints)))

; board? -> xexpr?
(define (visualize-board brd)
  (xexp table
    (tr (th) ,@(map colhints->xexpr (spec-col-hints (board-spec brd))))
    ,@(map row->xexpr (map board-line-line (board-rows brd)))))

; xexpr?
(define visualization-html-header
  (xexp head
    (meta #:charset "utf-8")
    (link #:rel "stylesheet" #:type "text/css" #:href "http://fonts.googleapis.com/css?family=Open+Sans:400,700,400italic,700italic")
    (link #:rel "stylesheet" #:type "text/css" #:href "style.css")
    (link #:rel "stylesheet" #:type "text/css" #:href "font-awesome.css")))

