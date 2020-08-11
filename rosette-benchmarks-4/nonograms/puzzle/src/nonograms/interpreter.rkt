#lang rosette/safe

(require
  (only-in racket error)
  rosette/lib/match
  rosette/lib/angelic
  "rules.rkt"
  "dsl-pretty.rkt"
  "action.rkt"
  "ast.rkt"
  "bindings.rkt"
  "../core/synth.rkt"
  "../core/util.rkt"
  "../core/lift.rkt")

(provide
  (struct-out binding)
  create-environment
  environment-line
  interpret/deterministic
  interpret/deterministic/nocondition
  condition-applies?/deterministic
  interpret/deterministic/single
  interpret/nondeterministic
  interpret/nondeterministic/concrete-env
  find-binding-for-pattern
  all-bindings-for-pattern
  binding-applies?
  evaluate-expression)

(struct environment (line gaps blocks) #:transparent)
(struct binding (type index value) #:transparent)
; expression: ListPattern?
; binding: binding?
(struct binding-info (expression binding) #:transparent)
(struct binding-lists (hints gaps blocks cell-indices cells) #:transparent)
; environment?, (listof? binding), (or/c false? integer?)
(struct interpstate (environment bindings local-binding) #:transparent)

; cartesian product: cons every element in front to each list in back
; equivalent to (for*/list ([x front] [l back]) (cons x l)), though the result will be backwards
(define (cp front back)
  (foldl
    (λ (x acc)
       (foldl (λ (l acc2) (cons (cons x l) acc2)) acc back))
    '()
    front))

; cartesian product of a list of lists
(define (cartesian-product lst)
  (if (ormap empty? lst)
      '()
      (foldr cp (list '()) lst)))

(define (op-of op)
  (match op ['+ +] ['- -] ['= =] ['> >] ['>= >=]))

(define (aggregate-of fn)
  (match fn ['max max] ['min min]))

(define (create-environment ctx)
  (environment
    ctx
    (gaps-of-line ctx)
    (blocks-of-line ctx)))

(define (get-hint env i)
  (define hints (line-hints (environment-line env)))
  (and (> (length hints) i) (list-ref hints i)))

(define (get-gap env i)
  (define gaps (environment-gaps env))
  (and (> (length gaps) i) (list-ref gaps i)))

(define (get-var its n)
  (define env (interpstate-environment its))
  (define ctx (environment-line env))
  (match n
   ['N (length (line-cells ctx))]
   ['K (length (line-hints ctx))]
   ['G (length (environment-gaps env))]
   ['B (length (environment-blocks env))]
   ))

(define (cell-index? its i)
  (define row (line-cells (environment-line (interpstate-environment its))))
  (and (integer? i) (>= i 0) (< i (length row))))

(define (get-cell its i)
  (define row (line-cells (environment-line (interpstate-environment its))))
  (list-ref row i))

(define (get-bndinfo its i)
  (list-ref (interpstate-bindings its) i))

(define (get-bnd fn its i)
  (fn (binding-info-binding (get-bndinfo its i))))

(define (eval-expr its expr)
  (define (evex e) (eval-expr its e))
  (define env (interpstate-environment its))
  (define ctx (environment-line env))
  ; Max? and Min? (same code except for one call)
  ; ((listof integer?) -> integer?), integer? -> boolean?
  (define (eval-optimal?-expr fn bnd)
    (define bi (get-bndinfo its bnd))
    (match (binding-info-expression bi)
     [(NoPattern) #f]
     [(Singleton _) #t]
     [_
      (define bnd (binding-info-binding bi))
      (define lst
        (match (binding-type bnd)
         ['none #f]
         ['hint (line-hints ctx)]
         ['gap (map segment-size (environment-gaps env))]
         ['block (map segment-size (environment-blocks env))]
         ; no other types are numeric
         [_ #f]))
      (and lst (= (binding-value bnd) (apply fn lst)))]))

  (match expr
   [(True) #t]
   [(Const v) v]
   [(Ident n) (get-var its n)]
   [(BindingIndex i) (get-bnd binding-index its i)]
   [(BindingValue i) (get-bnd binding-value its i)]
   [(Apply oper args)
    (define vals (map evex args))
    (and (&&map integer? vals) (apply (op-of oper) vals))]
   [(LowestEndCell hidx)
    (define hint-idx (evex hidx))
    (define hints (line-hints ctx))
    (and (integer? hint-idx)
         (>= hint-idx 0)
         (< hint-idx (length hints))
         ;(list-ref lec hint-idx))]
         (+ hint-idx (apply + (take hints (add1 hint-idx)))))]
   [(HighestStartCell hidx)
    (define hint-idx (evex hidx))
    (define hints (line-hints ctx))
    (define state (line-cells ctx))
    (and (integer? hint-idx)
         (>= hint-idx 0)
         (< hint-idx (length hints))
         ;(list-ref hsc hint-idx))]
         (- (length state) (+ (length hints) (- hint-idx) -1 (apply + (drop hints hint-idx)))))]
   [(Filled? idx val)
    (define i (evex idx))
    (and (cell-index? its i) (equal? val (get-cell its i)))]
   [(CellHasValue? c v)
    (equal? (get-bnd binding-value its c) v)]
   [(BoundValue) (interpstate-local-binding its)]
   ; with (BoundValue) set to pred, is bnd the only value in that binding class with the given condition?
   ; TODO this should set the bound index as well, otherwise it's unusable with the new types
   ; TODO when fixing this, be sure to fix the sketch as well, which currently blocks these
   ; (fortunately the BoundIndex is banned by the sketch, so it's an additive change, preserving old rules)
   [(Unique? bnd pred)
    (define (test x)
      (eval-expr (interpstate env (interpstate-bindings its) x) pred))
    (define lst
      (match (get-bnd binding-type its bnd)
       ['hint (line-hints ctx)]
       ['gap (map segment-size (environment-gaps env))]
       ['block (map segment-size (environment-blocks env))]
       ; TODO won't work for other types because on BoundValue is exposed
       [_ #f]))
    ;(dprintf "unique? ~v" lst)
    (and lst (test (get-bnd binding-value its bnd)) (= 1 (count test lst)))]
    ;(define filt (filter test lst))
    ;(and (= 1 (length filt)) (= (first filt) (get-bnd binding-value its bnd)))]
   ; is (BindingValue bnd) the maximum in that binding class?
   [(Max? bnd)
    (eval-optimal?-expr max bnd)]
   [(Min? bnd)
    (eval-optimal?-expr min bnd)]
   [(And left right)
    (and (evex left) (evex right))]))

(define (eval-condition its cnd)
  (define e (eval-expr its cnd))
  (equal? e #t))

(define (eval-action its actn)
  (match actn
   [(Fill val o s e)
    (define offset (eval-expr its o))
    (define start (eval-expr its s))
    (define end (eval-expr its e))
    (and (apply && (map integer? (list offset start end)))
         (fill-action val (+ offset start) (+ offset end)))]))

(define (all-binding-lists env)
  (define (seg->bnd typ s) (binding typ (segment-start s) (segment-size s)))
  (binding-lists
    ; hints
    (mapi (curry binding 'hint) (line-hints (environment-line env)))
    ; gaps
    (map (curry seg->bnd 'gap) (environment-gaps env))
    ; blocks
    (map (curry seg->bnd 'block) (environment-blocks env))
    ; cell indices
    (build-list/s (line-length (environment-line env)) (λ (i) (binding 'cell-index i #f)))
    ; cells
    (mapi (curry binding 'cell) (line-cells (environment-line env)))))

(define (get-binding-list all-lists type)
  (match type
   ['hint (binding-lists-hints all-lists)]
   ['gap (binding-lists-gaps all-lists)]
   ['block (binding-lists-blocks all-lists)]
   ['cell-index (binding-lists-cell-indices all-lists)]
   ['cell (binding-lists-cells all-lists)]))

(define (get-optimum fn lst)
  (define opt-val (apply fn (map binding-value lst)))
  (define (optimal? val x) (= (binding-value x) val))
  (filter (curry optimal? opt-val) lst))

; binding-lists?, Pattern? -> (listof binding-info?)
; evalutes a non-deterministic binding, given that the environment is concrete.
; resutls will be simple choices, so arbitrary-concretization is sufficient to get a valid result.
(define (evaluate-pattern bnd-lists bnd)
  (map
    (curry binding-info bnd)
    (match bnd
     [(NoPattern) (list (binding 'none #f #f))]
     [(ListPattern type)
      (define lst (get-binding-list bnd-lists type))
      (cond
       [(empty? lst) empty]
       [else
        (match bnd
         [(Singleton _)
          (if (empty? (cdr lst)) lst empty)]
         [(Constant _ i)
          (if (and (>= i 0) (< i (length lst))) (list (list-ref lst i)) empty)]
         [(Arbitrary _)
          lst])])])))

; like evaluate-binding, but returns integer indices into binding lists instead of binding-info?s
(define (evaluate-pattern/i bnd-lists bnd)
  (match bnd
   [(NoPattern) (list 0)]
   [(ListPattern type)
    (define lst (get-binding-list bnd-lists type))
    (cond
     [(empty? lst) empty]
     [else
      (match bnd
       [(Singleton _)
        (if (empty? (cdr lst)) (list 0) empty)]
       [(Constant _ i)
        ; if only constant is allowed, the assignment is actually "0" since interpret will filter the rest of the list.
        (if (and (>= i 0) (< i (length lst))) (list 0) empty)]
       [(Arbitrary _)
        (range/s 0 (length lst))])])]))

(define (deterministic-interp-impl fn prog env)
  ;(printf "~v\n" env)
  (define binding-exprs (Program-pattern prog))
  (define potential-bindings (map (curry evaluate-pattern (all-binding-lists env)) binding-exprs))
  ; for all possible combinations of bindings, run the program.
  (cond
   [(ormap empty? potential-bindings)
    #f]
   [else
    ; loop over all possible binding combinations
    (filter-map fn (cartesian-product potential-bindings))]))

; Program?, environment? -> (listof line-action?)
; interpret when both the program and environment are concrete.
; returns the set of possible interpretations, or empty? if there are none.
(define (interpret/deterministic prog env)
  (define (interp-for bindings)
    (define its (interpstate env bindings #f))
    (and (eval-condition its (Program-condition prog))
         (eval-action its (Program-action prog))))
  (deterministic-interp-impl interp-for prog env))

; interpret without bothering to check condition first (binding must still apply)
(define (interpret/deterministic/nocondition prog env)
  (define (interp-for bindings)
    (define its (interpstate env bindings #f))
    (eval-action its (Program-action prog)))
  (deterministic-interp-impl interp-for prog env))

; evaluates all basic parts of an expression, leaving connective operators
(define (evaluate-expression-terminals its expr)
  (define (rec e)
    (match e
     [(Apply oper args)
      (cons oper (map rec args))]
     [(And left right)
      (list '& (rec left) (rec right))]
     [_ (eval-expr its e)]))
  (rec expr))

(define (condition-applies?/deterministic prog env)
  (define (interp-for bindings)
    (define its (interpstate env bindings #f))
    (eval-condition its (Program-condition prog)))
  (not (empty? (deterministic-interp-impl interp-for prog env))))

; like interpret/deterministic, but assumes single outcome. errors if multiple
(define (interpret/deterministic/single prog env)
  (match (interpret/deterministic prog env)
   ['() #f]
   [#f #f]
   [(list x) x]
   [r (error (format "too many results! ~a ~v ~v" (debug-format-program prog) env r))]))

(struct result (bindings action) #:transparent)

; program?, environment?, (listof integer?) -> (or/c result? #f)
; interpret when the environment (and possibly the program) are symbolic.
(define (interpret/nondeterministic/full prog env #:binding-assignments [assn #f])
  (define potential-bindings (map (curry evaluate-pattern (all-binding-lists env)) (Program-pattern prog)))
  (cond
   [(lormap empty? potential-bindings)
    #f]
   [else
    ; angelicly choose a binding, or rely on the assignment
    (define bindings
      (cond
       [assn
        (map
          (λ (l i)
            (and (>= i 0) (< i (length l)) (list-ref l i)))
          potential-bindings
          assn)]
       [else
        (map (λ (l) (apply choose* l)) potential-bindings)]))
    (define bindings-okay? (andmap identity bindings))
    (define its (interpstate env bindings #f))
    (and
      bindings-okay?
      (result
        bindings
        (and
          (eval-condition its (Program-condition prog))
          (eval-action its (Program-action prog)))))]))

(define (interpret/nondeterministic prog env #:binding-assignments [assn #f])
  (define r (interpret/nondeterministic/full prog env #:binding-assignments assn))
  (and r (result-action r)))

; interpret when the program is symbolic but the environment is concrete.
(define (interpret/nondeterministic/concrete-env prog env #:binding-assignments [assn #f])
  (interpret/nondeterministic prog env #:binding-assignments assn)) ; they're currently the same

; (listof? Binding?), line? -> (or/c false? (listof binding?))
; evaluates the given pattern, returning a (symbolically chosen) set of bindings
(define (find-binding-for-pattern bndlst ctx)
  (define env (create-environment ctx))
  (define potential-bindings (map (curry evaluate-pattern (all-binding-lists env)) bndlst))
  (cond
   [(lormap empty? potential-bindings) #f]
   [else
    ; angelicly choose a binding
    (map (λ (l) (apply choose* l)) potential-bindings)]))

; Program?, environment? -> (or/c false? (listof (listof integer?)))
; returns all possible bindings (as index lists, to be used with #:binding-assignments) for the given program/environment
(define (all-bindings-for-pattern prog env)
  (define potential-bindings (map (curry evaluate-pattern/i (all-binding-lists env)) (Program-pattern prog)))
  (cond
   [(lormap empty? potential-bindings) #f]
   [else (cartesian-product potential-bindings)]))

(define (binding-applies? prog env)
  (define potential-bindings (map (curry evaluate-pattern (all-binding-lists env)) (Program-pattern prog)))
  (not (lormap empty? potential-bindings)))

; Expr?, line? -> any?
; evaluate a expression. really only for unit testing.
(define (evaluate-expression expr ctx)
  (eval-expr (interpstate (create-environment ctx) empty #f) expr))


