#lang racket

; Some rewrite rules/peehole optimizations to make synthesized programs easier to read.
; This is all very standard basic stuff like constant folding.

(provide apply-all-rewrite-rules)

(require
  "ast.rkt"
  "compile.rkt")

(define (rewrite-constant-folding prog)
  (define (rewrite expr)
    (match expr
     [(Apply '+ (list (Const x) (Const y)))
      (Const (+ x y))]
     [(Apply '- (list (Const x) (Const y)))
      (Const (- x y))]
     [(Apply '+ (list (Const 0) e))
      e]
     [(Apply '+ (list e (Const 0)))
      e]
     [(Apply '- (list e (Const 0)))
      e]
     [(Apply '+ (list (Apply '+ (list (Const x) e)) (Const y)))
      (rewrite (Apply '+ (list (Const (+ x y)) e)))]
     [_ expr]))
  (program-map-expressions-postorder rewrite prog))

(define (rewrite-clearner-arithmetic prog)
  (define (rewrite expr)
    (match expr
     [(Apply '+ (list (Const x) e)) #:when (< x 0)
      (Apply '- (list e (Const (- x))))]
     [(Apply '- (list e (Const x))) #:when (< x 0)
      (Apply '+ (list e (Const (- x))))]
     [(Apply '> (list (Const -1) (Apply '- (list x y))))
      (Apply '> (list (Apply '- (list y x)) (Const 1)))]
     [_ expr]))
  (program-map-expressions-postorder rewrite prog))

; Chagnes the fill action so the offset is zero, to align with the paper's simplified syntax.
; That is, given (fill v o s e), changes it to (fill v 0 (+ o s) (+ o e)).
; This allows for further simplification before pretty-printing (which will omit an offset of 0).
(define (clear-offset prog)
  (match prog
   [(Program p c (Fill v o s e))
    (Program p c (Fill v (Const 0) (Apply '+ (list o s)) (Apply '+ (list o e))))]))


(define (apply-all-rewrite-rules prog)
  ((compose1
    rewrite-clearner-arithmetic
    rewrite-constant-folding
    clear-offset)
   prog))

