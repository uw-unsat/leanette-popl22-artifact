#lang rosette

(define (echo x) (pretty-print (enumtree->expression x)))

(define (fmap f l)
  (if (pair? l)
    (cons (f (car l)) (fmap f (cdr l)))
    l))


; http://www.scala-lang.org/blog/2016/02/03/essence-of-scala.html

(require "tree-lib.rkt")
(require "bounded.rkt")
(current-bound! 3)

(define dot-stx
  '([defn (val . (name . term))
          (typ . (name . type))
          (and . (defn . defn))
    ]
    [term 
;         (get . (term . name))
          (let . ((name . (type . type)) . (term . term)))
          defn
          (var . name)
          null
          (die . term)

          (make-null . type)
    ]
    [type Any
          Nothing

          (get . (term . name))

          (typ . (name . type))
          (val . (name . type))
          (and . (type . type))

;         (range . (type . type))
          (typ . (name . (range . (type . type))))
    ]
    [name a b c]
    ))

;(nonterminals! '(die))

(define (harvest syntax)
  (define (terminal-nodes tree)
    (if (pair? tree)
      (append (terminal-nodes (car tree))
              (terminal-nodes (cdr tree)))
      (list tree)))
  (remove-duplicates
    (filter
      (lambda (x)
        (and (not (null? x))
             (not (member x (map car syntax)))))
      (terminal-nodes syntax))))

(nonterminals! (harvest dot-stx))

(define (make! node depth)
    (define t** (binary-tree! depth))
    (assert (syntax-matches? dot-stx node t**))
    t**)

(define (freshen! x)
  (define x* (binary-tree! 6))
  (if (equal? x* x)
    x*
    #f))



(define d-empty (cons #f #f))

(define (d-find kind tbl name)
  (tree-match
    tbl
    '(and . (_ . _))
    (lambda (l r)
      (or (d-find kind l name)
          (d-find kind r name)))

    '(_ . _)
    (lambda (k v)
      (if (equal? (cons kind name) k)
        v
        #f))))

(define (d-make kind name val)
  (cons (cons kind name) val))

(define (d-join l r)
    (cons (symbol->enum 'and) (cons l r)))

(define (d-eval-expr e env)
  (tree-match
    e
;   '(get . (_ . _))
;   (lambda (tbl name)
;     (d-find 'value (d-eval-expr tbl env) name))

    '(let . ((_ . (_ . _)) . (_ . _)))
    (lambda (name intype outtype value expr)
      (d-eval-expr
        expr
        (table-add env name (d-eval-expr value env))))

    '(val . (_ . _))
    (lambda (name term)
      (d-make 'value name (d-eval-expr term env)))

    '(typ . (_ . _))
    (lambda (foo bar) d-empty)

    '(and . (_ . _))
    (lambda (a b)
      (d-join
        (d-eval-expr a env)
        (d-eval-expr b env)))

    '(var . _)
    (lambda (name)
      (table-find env name))

    '(die . _)
    (lambda (x) (assert #f "ClassCastException"))

    '(make-null . _)
    (lambda (x) 1337)

    'null
    (lambda () 123)))


(define/rec (d-reduce-type type env [strict? #t])
    (tree-match
        type
        'Any
        (lambda () type)

        'Nothing
        (lambda () type)

        '(and . (_ . _))
        (lambda (a b)
          (assert (not strict?) "Checking bounds")
          (d-join
            (d-reduce-type a env)
            (d-reduce-type b env)))

        '(get . (_ . _))
        (lambda (tbl name)
          (d-find 'type
                  (d-type-expr tbl env) name))

        '(typ . (_ . _))
        (lambda (name t)
            (d-make 'type name (d-reduce-type t env)))

        '(val . (_ . _))
        (lambda (name t)
            (d-make 'value name (d-reduce-type t env)))

        '(range . (_ . _))
        (lambda (from to)
          (cons (symbol->enum 'range)
                (cons
                  (d-reduce-type from env)
                  (d-reduce-type to env))))
        ))

(define/rec (d-subtype? sub sup)
  (tree-match
    (cons sub sup)
    '(_ . Any) (lambda (x) #t)

    '(Nothing . _) (lambda (x) #t)

    '((and . (_ . _)) . _)
    (lambda (l r sup+)
      (or (d-subtype? l sup) (d-subtype? r sup)))

    '(_ . (and . (_ . _)))
    (lambda (sub+ l r)
      (and (d-subtype? sub l) (d-subtype? sub r)))

    '((range . (_ . _)) . _)
    (lambda (lower upper r)
        (d-subtype? upper r))

    '(_ . (range . (_ . _)))
    (lambda (l lower upper)
        (d-subtype? l lower))

;   This is actually too restrictive, it should check if they're both the same
;   `value` or the same `type` or something.
    '_
    (lambda (x) (equal? sub sup))
    ))


(define (d-mutex-helper kind x y)
  (and
    (not (and (d-find kind x (symbol->enum 'a))
              (d-find kind y (symbol->enum 'a))))
    (not (and (d-find kind x (symbol->enum 'b))
              (d-find kind y (symbol->enum 'b))))
    (not (and (d-find kind x (symbol->enum 'c))
              (d-find kind y (symbol->enum 'c))))
    ))

(define (d-mutex x y)
    (and (d-mutex-helper 'value x y)
         (d-mutex-helper 'type  x y)))


(define (d-type-expr e env)
    (tree-match
      e
;     '(get . (_ . _))
;     (lambda (tbl name)
;       (define result
;         (d-find
;           'value
;           (d-type-expr tbl env)
;           name))
;       (assert result)
;       result)

      '(let . ((_ . (_ . _)) . (_ . _)))
      (lambda (name intype outtype value expr)
        (define iT (d-reduce-type intype env))
        (define iT+ (d-type-expr value env))
        (assert (d-subtype? iT+ iT) "Let type fail 1")

        (define oT (d-reduce-type outtype
            (table-add env name iT)))
        (define oT+ (d-type-expr expr
            (table-add env name iT)))
        (assert (d-subtype? oT+ oT) "Let type fail 2")

        (d-reduce-type outtype (table-add env name iT+))
        )

      '(val . (_ . _))
      (lambda (name term)
        (define t (d-type-expr term env))
        (d-make 'value name t))

      '(typ . (_ . _))
      (lambda (name term)
        (define t (d-reduce-type term env))
        (d-make 'type name t))

      '(and . (_ . _))
      (lambda (a b)
        (assert #f "Checking bounds")
        (define t-a (d-type-expr a env))
        (define t-b (d-type-expr b env))
;       (assert (d-mutex t-a t-b) "Table mutex")
        (d-join t-a t-b))

      '(var . _)
      (lambda (name)
        (define t (table-find env name))
        (assert t "Name not found!")
        t)

      '(die . _)
      (lambda (name)
        (define t (d-type-expr name env))
        (assert (d-subtype? t (symbol->enum 'Nothing)) "Well then.")

        t)
      
      '(make-null . _)
      (lambda (t)
        (define t+ (d-reduce-type t env #f)) ; non-strict!
        (assert t+)
        (assert (not (d-subtype? t+ (symbol->enum 'Nothing))) "Ugh")
        t+)

      'null
      (lambda () (symbol->enum 'Any))
      ))

(define d-test-expr
  (expression->enumtree
;   '(typ b get (get (get Nothing . b) . b) . b)
;   '(get (and (typ b . Any) typ b . Any) . b)
;   '(let . ( (a . Any) . (null . null) ) )
;   '(get . (
;       (let . ( (d . (get . ((var . b) . c))) . (null . (var . d) ) ) )
;    . a))
;   '(let (c . Nothing) (typ b typ c . Nothing) get (get (var . c) . b) . c)
;   '(get (get (val d val c . null) . d) . c)
;   '(get . (
;       (let . ( ( d . (Any . (and . ((val . (a . Any)) . Any))) ) .
;                ( null . (var . d) ) ) )
;   . a))
    '(die . (let . ( (b . ((typ . (a . Any)) . (get . ((var . b) . a)))) . ((and . ( (typ . (a . Nothing)) . (typ . (a . Any)) )) . null))))

#|
'(die
   .
   (let . (
           (a .
              ((and .
                    ((typ . (T-A . (range . (Any . T-B))))
                     .
                     (typ . (T-B . (range . (T-A . Nothing))))))
               .
               Any)
              ) .
           ( null . null ))))|#

    ))


#|
(define (depth t)
    (if (pair? t)
        (+ 1 (max (depth (car t)) (depth (cdr t))))
        1))
(display "Depth...")
(displayln (depth d-test-expr))

(displayln "stx  test...")
(assert (syntax-matches? dot-stx 'term d-test-expr) "Test stx")
(displayln "type test...")
(echo (d-type-expr d-test-expr '()))
(displayln "eval test...")
(echo (d-eval-expr d-test-expr '()))
|#

(require rosette/solver/smt/boolector (only-in rosette current-solver))
(current-solver (boolector))

(time (begin
(displayln "Building tree...")
(define t* (time (make! 'term 10)))
(displayln "Built tree...")

(displayln "Checking type...")
(void (time (d-type-expr t* '())))
;(assert (equal? (time (d-type-expr t* '())) (symbol->enum 'Nothing)))
(displayln "Checked type...")

(displayln "Verifying...")
(define sol (verify (d-eval-expr t* '())))
(displayln (sat? sol))))
