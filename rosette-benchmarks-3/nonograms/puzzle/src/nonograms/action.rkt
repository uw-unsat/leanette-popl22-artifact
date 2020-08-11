#lang rosette/safe

(provide (all-defined-out))

(require
  (only-in racket match-define raise-argument-error hasheq)
  "rules.rkt"
  "../core/core.rkt")

; filling a contiguous run of cells with value in range [start, end)
(standard-struct fill-action (value start end))
; line + end cells
(standard-struct line-transition (start end-cells))
; line + fill-action, like transition but only for actions representible by fill-action.
(standard-struct line/fill (line action))

(define (line-transition-end trns)
  (match-define (line-transition (line h _) c) trns)
  (line h c))

; the number of cells changed in a transition
(define (line-transition-size trns)
  (count (λ (s e) (not (equal? s e)))
         (line-cells (line-transition-start trns))
         (line-transition-end-cells trns)))

(define (fill-action->string actn)
  (match-define (fill-action v s e) actn)
  (format "(fill ~a [~a ~a))" v s e))

(define (transition->json ctx)
  (define (cell->json c) (if (empty-cell? c) 'null c))
  (match-define (line-transition (line h s) e) ctx)
  (hasheq 'start (map cell->json s)
          'final (map cell->json e)
          'hints h))

; fill-action?, line-transition? -> boolean?
; returns true iff (line-weaker? (apply-action action (line-transition-start-line transition)) (line-transition-end-line transition)),
; except it's much more efficient, especially for rosette.
; TODO optimize me
(define (action-compatible-with-transition? action transition)
  (assert transition)
  (cond
   [action
    (match-define (fill-action val si ei) action)
    (match-define (line-transition _ end-state) transition)
    (define len (length end-state))
    (when (symbolic? len)
      (raise-argument-error 'action-compatible-with-transition? "(not/c symbolic?)" len))
    (define (check idx)
      (define eval (list-ref end-state idx))
      (||
        (< idx si)
        (>= idx ei)
        (equal? eval val)))
    (and
      (integer? si)
      (integer? ei)
      (>= si 0)
      (<= ei len)
      (< si ei) ; NOTE: commented out because the interpreter shouldn't ever return fills that don't meet this criteria.
      (&&map check (range/s 0 len)))]
   [else #f]))

; fill-action?, line-transition? -> boolean?
; returns true iff (and (action-compatible-with-transition? action transition) (action has non-zero impact)).
(define (action-compatible-with-and-impactful-for-transition? action transition)
  ;(dprintf "actn: ~v\ntctx: ~v" action transition)
  (match-define (fill-action _ s e) action)
  (match-define (line-transition (line _ cells) _) transition)
  (&&
    (action-compatible-with-transition? action transition)
    (lormapi
      (λ (i c)
        (&& (<= s i) (< i e) (empty-cell? c)))
      cells)))

; fill-action?, line? -> line?
(define (apply-action action ctx)
  (match-define (fill-action val start end) action)
  (define end-cells
    (mapi
      (λ (i v) (if (and (>= i start) (< i end)) val v))
      (line-cells ctx)))
  (line (line-hints ctx) end-cells))

; context-delta? -> context-transition?
(define (line/fill->transition dctx)
  (match-define (line/fill ctx (fill-action val start end)) dctx)
  (define end-cells
    (mapi
      (λ (i v) (if (and (>= i start) (< i end)) val v))
      (line-cells ctx)))
  (line-transition ctx end-cells))

; is to-check <= other, according to subset relationship
(define (action-weaker? to-check other)
  (match-define (fill-action v1 s1 e1) to-check)
  (match-define (fill-action v2 s2 e2) other)
  (and (equal? v1 v2)
       (<= s2 s1)
       (>= e2 e1)))

