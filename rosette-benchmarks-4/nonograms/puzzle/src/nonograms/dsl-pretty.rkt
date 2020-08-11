#lang racket

(provide (all-defined-out))

(require
  "../core/core.rkt"
  racket/struct
  "ast.rkt")

(define-syntax-rule (program bindings ... condition action)
  (Program (list bindings ...) condition action))

(define-syntax-rule (app oper args ...)
  (Apply 'oper (list args ...)))

(define-syntax-rule (a+ args ...) (app + args ...))
(define-syntax-rule (a- args ...) (app - args ...))
(define-syntax-rule (a= args ...) (app = args ...))
(define-syntax-rule (a> args ...) (app > args ...))
(define-syntax-rule (a>= args ...) (app >= args ...))

(define C0 (Const 0))
(define C1 (Const 1))
(define CM1 (Const -1))
(define C2 (Const 2))
(define C3 (Const 3))
(define C4 (Const 4))
(define C5 (Const 5))

(define N (Ident 'N))
(define K (Ident 'K))
(define G (Ident 'G))
(define BI (BindingIndex 0))
(define BV (BindingValue 0))
(define SI (BindingIndex 1))
(define SV (BindingValue 1))
(define TI (BindingIndex 2))
(define TV (BindingValue 2))
(define FI (BindingIndex 3))
(define FV (BindingValue 3))

(define (pretty-format-program prog)
  (define (expand name args) (cons name (map pretty-format-program args)))
  (define (rename name . args) (expand name args))
  (match prog
   [(Const x) x]
   [(Ident n) n]
   [(Apply op args) (expand op args)]
   [(NoPattern) '_]
   [(BindingIndex i) `(Idx ,i)]
   [(BindingValue i) `(Val ,i)]
   [(? symbol?) prog]
   [(? struct?)
    (define name (struct-name prog))
    (define args (struct->list prog))
    (cons name (map pretty-format-program args))]
   [(? list?)
    (map pretty-format-program prog)]
   [_ prog]))

(define (debug-format-program prog)
  ; substring to chop off the leading '
  ;(substring (format "~a" (pretty-format-program prog)) 1))
  (format "~a" (pretty-format-program prog)))


(define (pretty-print-program p #:columns [col-len 60])
  (parameterize ([pretty-print-columns col-len]
                 [pretty-print-current-style-table
                   (pretty-print-extend-style-table
                     (pretty-print-current-style-table)
                     '(Fill Unique?)
                     '(define define))])
    (pretty-format (pretty-format-program p))))

; Program?, string? -> string?
; convert a program to the stylized python-like syntax.
(define (program->stylized-string prog name)
  (error "unimplemented"))

;; HACK by james
(define-syntax-rule (xexp . args) #f)


; Program? -> xexpr?
; convert a program to the stylized python-like syntax, but as html with styling information.
(define (program->stylized-html prog name)
  (define (kw text)
    (xexp span #:class "kw" ,text))
  (define (fun text)
    (xexp span #:class "fun" ,text))
  (define (var text)
    (xexp span #:class "var" ,text))
  (define (fundecl text)
    (xexp span #:class "fundecl" ,text))
  (define (const_ text)
    (xexp span #:class "const" ,text))
  (define (op->html op)
    (match op
     ['>= "≥"]
     [_ op]))

  (define current-bount-var (box (void)))

  ; Calculate semi-readable variable names for each pattern element.
  ; We do hints -> h, blocks -> b, gaps -> g.
  (define (varname i)
    (define n
      (match (list-ref (Program-pattern prog) i)
       [(ListPattern 'hint) "h"]
       [(ListPattern 'block) "b"]
       [(ListPattern 'gap) "g"]
       [(ListPattern 'cell-index) "i"]
       [(ListPattern 'cell) "c"]))
    (var (format "~a~a" n i)))

  (define (expr->html e)
    (match e
     [(Singleton t)
      (list (fun "singleton") "(" (kw t) ")")]
     [(Constant t i)
      (list (fun "constant") "(" (kw t) ", " (format "~a" i) ")")]
     [(Arbitrary t)
      (list (fun "arbitrary") "(" (kw t) ")")]
     [(Fill v o s e)
      (match o
       [(Const 0)
        `(,(kw "fill(") ,@(expr->html v) ", " ,@(expr->html s) ", " ,@(expr->html e) ")")]
       [_
        `(,(kw "fill(") ,@(expr->html v) ", " ,@(expr->html o) " + " ,@(expr->html s) ", " ,@(expr->html o) " + " ,@(expr->html e) ")")])]
     [(True)
      (list (kw "true"))]
     [(? boolean?)
      (list (kw (if e "true" "false")))]
     [(? integer?)
      (list (format "~a" e))]
     [(Ident 'N)
      (list (const_ 'line_size))]
     [(Ident n)
      (list (const_ n))]
     [(Const v)
      (expr->html v)]
     [(BindingIndex i)
      (list (fun "start") "(" (varname i) ")")]
     [(BindingValue i)
      (list (fun "size") "(" (varname i) ")")]
     [(Apply binop (list e1 e2))
      (define base `(,@(expr->html e1) " " ,(op->html binop) " " ,@(expr->html e2)))
      (define requires-parens? (member binop '(-)))
      (if requires-parens? (cons "(" (append base '(")"))) base)]
     [(And e1 e2)
      `(,@(expr->html e1) ,(kw " and ") ,@(expr->html e2))]
     [(Max? i)
      (list (fun "maximal") "(" (varname i) ")")]
     [(Min? i)
      (list (fun "minimal") "(" (varname i) ")")]
     [(LowestEndCell (BindingIndex e))
      (list (fun "lowest_end_cell") "(" (varname e) ")")]
     [(HighestStartCell (BindingIndex e))
      (list (fun "highest_start_cell") "(" (varname e) ")")]
     [(Unique? i expr)
      (set-box! current-bount-var (varname i))
      `("(" ,(varname i) ,(kw " is unique where " ) ,@(expr->html expr) ")")]
     [(Filled? i v)
      `("Filled?(" ,@(expr->html i) "," ,@(expr->html v) ")")]
     [(CellHasValue? i v)
      `("CellHasValue?(" ,(varname i) "," ,@(expr->html v) ")")]
     [(BoundValue)
      (list (unbox current-bount-var))]
     [e (list (xexp span #:style "color: red; font-weight: bold" ,(format "~a" e)))]))

  (define (pattern->html i pat)
    (define terminal
      (if (= (add1 i) (length (Program-pattern prog)))
          ":"
          (kw " and")))
    (append (list "\t\t" (varname i) " = ") (expr->html pat) (list terminal "\n")))

  (xexp pre
    ,(kw "def") " " ,(fundecl name) ":\n"
    "\t" ,(kw "with") "\n" ,@(append-mapi pattern->html (Program-pattern prog))
    "\t" ,(kw "if ") ,@(expr->html (Program-condition prog)) ":\n"
    "\t" ,(kw "then ") ,@(expr->html (Program-action prog)) "\n"

  ))


