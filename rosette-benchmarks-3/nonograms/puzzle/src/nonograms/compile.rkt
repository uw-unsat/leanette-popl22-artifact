#lang rosette/safe

(provide
  program-map-expressions-postorder
  features-used-by-program
  program-limited-to-features?
  strip-unused-patterns
  same-pattern?)

(require
  (only-in racket error set=? mutable-seteq mutable-set set-add! set-member? set->list struct-copy exit set-subtract set-empty? for)
  rosette/lib/match
  "rules.rkt"
  "action.rkt"
  "ast.rkt"
  "dsl-pretty.rkt"
  "../core/core.rkt")

; list of all expressions (Expr?) part of this program, including non-terminal expressions
; (so subexpressions appear both in the list and as part of other elements of the list).
(define (program-for-each-expr f prog)
  (define (rec p) (program-for-each-expr f p))
  (match prog [(Expr) (f prog)] [_ (void)])
  (match prog
   [(Program _ cnd act)
    (rec cnd)
    (rec act)]
   [(Fill _ offset start end)
    (rec offset)
    (rec start)
    (rec end)]
   [(Filled? e _) (rec e)]
   [(HighestStartCell e) (rec e)]
   [(LowestEndCell e) (rec e)]
   [(And l r)
    (rec l)
    (rec r)]
   [(Apply _ args) (for-each rec args)]
   [(Unique? i e) (rec e)]
   [(TerminalExpr) (void)]))

(define (program-map-expressions f prog)
  (match prog
   [(Program pat cnd act)
    (Program pat (f cnd) (f act))]
   [(Fill v offset start end)
    (Fill v (f offset) (f start) (f end))]
   [(Filled? e v)
    (Filled? (f e) v)]
   [(CellHasValue? e v)
    (CellHasValue? e v)]
   [(HighestStartCell e)
    (HighestStartCell (f e))]
   [(LowestEndCell e)
    (LowestEndCell (f e))]
   [(And l r)
    (And (f l) (f r))]
   [(Apply op args)
    (Apply op (map f args))]
   [(Unique? i e)
    (Unique? i (f e))]
   [(TerminalExpr)
    prog]))

; Recurses over the structure of the given program, invoking f on each subexpression.
; Will recurse on the subexpresions, replacing the sub-expressions with any new value.
; Then will invoke f on the resulting new expression.
; If f returns a non-false value, the expression will be replaced with that return value.
; Otherwise it will be the result of the recursive call.
(define (program-map-expressions-postorder f prog)
  (define v (program-map-expressions (curry program-map-expressions-postorder f) prog))
  (f v))

; Program? -> (listof symbol?)
(define (features-used-by-program prog)
  (define used (mutable-seteq))
  ; Apply has to be handled in a special manner because it overloads several features
  (define (visit s)
    (match s
     [(Apply op _)
      (set-add! used (feature-of-operator op))]
     [_ (set-add! used (feature-of-ast-element s))]))
  (program-for-each-expr visit prog)
  ; have to add pattern features specially
  (for ([p (Program-pattern prog)])
    (match p
     ; assumes the type name is the same as the feature name (which is true)
     [(ListPattern t) (set-add! used t)]
     [(NoPattern) (void)]))
  (set->list used))

(define (program-limited-to-features? features prog)
  (set-empty? (set-subtract (features-used-by-program prog) features)))

; Program? -> Program?
; replaces any unferenced pattern with (NoPattern)
(define (strip-unused-patterns prog)
  (define used-bindings (mutable-set))
  (define (get e)
    (match e
     [(BindingIndex i) i]
     [(BindingValue i) i]
     [(Unique? i _) i]
     [_ #f]))
  (program-for-each-expr
    (λ (e)
      (define x (get e))
      (when x (set-add! used-bindings x)))
    prog)
  (define new-patterns
    (mapi
      (λ (i b)
        (if (set-member? used-bindings i)
            b
            (NoPattern)))
      (Program-pattern prog)))
  (struct-copy Program prog [pattern new-patterns]))

; Program?, Program? -> boolean?
; not rosette safe
(define (same-pattern? p1 p2)
  (set=? (Program-pattern p1) (Program-pattern p2)))

