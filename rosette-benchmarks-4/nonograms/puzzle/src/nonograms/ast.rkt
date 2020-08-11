#lang rosette/safe

(provide
  (except-out
    (all-defined-out)
    define-ast
    define-feature
    feature-set
    register-ast-element
    feature->asts
    ast->feature))

(require
  rosette/lib/match
  (for-syntax racket/syntax)
  (only-in racket
           local-require make-hash make-immutable-hash hash-set! hash-ref hash-has-key?
           mutable-seteq set-add! set-count hash-keys error)
  "../core/core.rkt")

; mapping from feature name to whether its in the default set
(define feature-set (make-hash))
(define feature->asts (make-hash))
(define ast->feature (make-hash))

(define (register-ast-element f sname)
  (unless (hash-has-key? feature-set f)
    (error (format "ast element registered with undeclared feature '~a'" f)))
  (hash-set! feature->asts f (cons sname (hash-ref feature->asts f empty)))
  (hash-set! ast->feature sname f))

(define-syntax (define-ast stx)
  (syntax-case stx ()
   [(_ name feature (fields ...))
    #'(begin
      (register-ast-element 'feature 'name)
      (standard-struct name (fields ...)))]
   [(_ name feature supertype (fields ...))
    #'(begin
      (register-ast-element 'feature 'name)
      (standard-struct name supertype (fields ...)))]))

; equivalent of:
; (define-feature xyz b) ~> (define feature-xyz 'xyz b)
; also adds the feature to the global feature hash table
(define-syntax (define-feature stx)
  (syntax-case stx ()
   [(_ sym default?)
    (with-syntax ([name (format-id #'sym "feature-~a" (syntax-e #'sym))])
      #'(begin
        (hash-set! feature-set 'sym default?)
        (define name 'sym)))]))

(define-feature base #t)
(define-feature unique #t)
(define-feature optimal #t)

(standard-struct Expr ())
; we distinguish exprs that have children from those that don't to make function that iterate over all exprs more robust to changes.
(standard-struct TerminalExpr Expr ())
(define-ast True base TerminalExpr ())
(define-ast Const base TerminalExpr (val))
(define-ast Ident base TerminalExpr (name))
(define-ast BindingIndex base TerminalExpr (name))
(define-ast BindingValue base TerminalExpr (name))
(define-ast Apply base Expr (oper args))

(define-ast BoundValue unique TerminalExpr ())
(define-ast Unique? unique Expr (binding pred))
(define-ast Max? optimal TerminalExpr (binding))
(define-ast Min? optimal TerminalExpr (binding))

(define-feature filled #f)
(define-feature fits #f)

; TODO reintegrate
(define-ast Filled? filled Expr (idx val))
; TODO implement support for
(define-ast Fits? fits Expr (hint gap))

(define-feature and #t)

(define-ast And and Expr (left right))

(define-feature geometry #t)

(define-ast LowestEndCell geometry Expr (hint-index))
(define-ast HighestStartCell geometry Expr (hint-index))

(define-feature hint #t)
(define-feature gap #t)
(define-feature block #t)
(define-feature cell-index #f)
(define-feature cell #f)

(define-ast CellHasValue? cell TerminalExpr (binding val))

(standard-struct Pattern ())
(standard-struct NoPattern Pattern ())
(standard-struct ListPattern Pattern (type))
(define-ast Arbitrary base ListPattern ())
(define-ast Constant base ListPattern (idx))
(define-ast Singleton base ListPattern ())

; fill with val in [offset + start, offset + end)
(define-ast Fill base (val offset start end))

(define-ast Program base (pattern condition action))

(define-feature line-length #t)
(define-feature hint-length #f)

(define-feature arithmetic #t)
(define-feature comparison #t)

(define all-program-features (hash-keys feature-set))
(define default-program-features (filter (curry hash-ref feature-set) all-program-features))

(define (feature-of-ast-element x)
  (hash-ref ast->feature (struct-name x)))

(define (feature-of-operator x)
  (match x
   [(or '+ '-) 'arithmetic]
   [(or '= '> '>=) 'comparison]))

; symbol? -> symbol?
; what is the type of values for this pattern?
(define (pattern-value-type ptype)
  (match ptype
   ['hint 'size]
   ['gap 'size]
   ['block 'size]
   ['cell-index 'void]
   ['cell 'cell]))

; symbol? -> symbol?
; what is the type of indices for this pattern?
(define (pattern-index-type ptype)
  (match ptype
   ['hint 'hint]
   ['gap 'cell]
   ['block 'cell]
   ['cell-index 'cell]
   ['cell 'cell]))

(define (program-cost p)
  (define (sum e) (apply + (map program-cost e)))
  (define (add . a) (apply + (map (λ (x) (if (integer? x) x (program-cost x))) a)))
  (match p
   [(True) 0]
   [(Const _) 1]
   [(Ident _) 2]
   [(BindingIndex _) 1]
   [(BindingValue _) 1]
   [(Apply _ args) (+ 1 (sum args))]
   [(Filled? i _) (add 2 i)]
   [(CellHasValue? i _) (add 1 i)]
   [(Fits? h g) (add 0 h g)]
   [(And l r) (add 1 l r)]
   [(BoundValue) 1]
   [(Unique? _ e) (add 2 e)]
   [(Max? _) 7]
   [(Min? _) 7]
   [(LowestEndCell e) (add 6 e)]
   [(HighestStartCell e) (add 6 e)]
   [(Fill _ o s e) (add o s e)]
   [(NoPattern) 0]
   [(Arbitrary lst) 6]
   [(Singleton lst) 7]
   [(Constant lst idx) (add 8 idx)]
   [(Program b c a) (add (sum b) c a)]))

; true iff the given program references all of its bindings
(define (program-uses-all-bindings? prog)
  (define used (mutable-seteq))

  (define (rec expr)
    (match expr
     [(BindingIndex i) (set-add! used i)]
     [(BindingValue i) (set-add! used i)]
     [(Apply _ args) (for-each rec args)]
     [(And l r) (rec l) (rec r)]
     [(Unique? _ e) (rec e)]
     [(Max? i) (set-add! used i)]
     [(Min? i) (set-add! used i)]
     [(LowestEndCell e) (rec e)]
     [(HighestStartCell e) (rec e)]
     [(Fill _ o s e) (map rec (list o s e))]
     [_ (void)]))

  (rec (Program-condition prog))
  (rec (Program-action prog))

  (= (set-count used) (length (Program-pattern prog))))

