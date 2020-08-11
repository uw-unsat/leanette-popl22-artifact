#lang racket

(provide (all-defined-out))
(require (prefix-in rosette: rosette)
         "lib.rkt")

(define (parse-term type t)
  (match* (type t)
    [('int (? number?)) (values t 1)]
    [('bool #true) (values #true 1)]
    [('bool #false) (values #false 1)]
    [(_ `(var ,x)) (values (make-symbolic-var type x) 1)]
    [(_ `(ite ,c ,t ,e))
     ; important: we don't want to evaluate t and e under c, so
     ; evaluate them all first
     (define-values [ec c-stat] (parse-term 'bool c))
     (define-values [et t-stat] (parse-term type t))
     (define-values [ee e-stat] (parse-term type e))
     (values (rosette:if ec et ee) (+ c-stat t-stat e-stat 1))]
    [(_ `(expr ,o ,l ,r))
     (define-values [el l-stat] (parse-term 'int l))
     (define-values [er r-stat] (parse-term 'int r))
     (values
      ((match o
         ['add rosette:+]
         ['mul rosette:*]
         ['lt rosette:<]
         ['eq rosette:=])
       el
       er)
      (+ l-stat r-stat 1))]))

(define (parse-state s)
  (match-define `(state ,assumes ,asserts) s)
  (define-values [assumes-val assumes-stat] (parse-term 'bool assumes))
  (define-values [asserts-val asserts-stat] (parse-term 'bool asserts))
  (values (state assumes-val asserts-val) (+ assumes-stat asserts-stat)))

(define (parse-union gvs)
  (match gvs
    [(list `(choice ,g ,v) gvs ...)
     (define-values [eg _] (parse-term 'bool g))
     (define ev (parse-val v))
     (define gvs* (parse-union gvs))
     (rosette:if eg ev gvs*)]
    [(list) (undef)]))

(define (parse-list xs)
  (match xs
    [(list x xs ...)
     (define x* (parse-val x))
     (define xs* (parse-list xs))
     (cons x* xs*)]
    [(list) '()]))

(define (parse-var x) (string->symbol (format "x~a" x)))

(define (parse-ast t)
  (match t
    [`(let0 ,x ,v ,b)
     `(let ([,(parse-var x) ,(parse-ast v)])
        ,(parse-ast b))]
    [`(datum (op.lang.datum.int ,x)) x]
    [`(if0 ,c ,t ,e)
     `(if ,(parse-var c)
          ,(parse-ast t)
          ,(parse-ast e))]
    [`(app ,o ,xs ...)
     `(,o ,@(for/list ([x xs]) (parse-var x)))]
    [`(call ,f ,a) `(,(parse-var f) ,(parse-var a))]
    [`(var ,x) (parse-var x)]
    [#t #t]
    [#f #f]
    [`(λ ,x ,b) `(lam ,(parse-var x) ,(parse-ast b))]
    [`(make-error) `(assert #f)]
    [`(make-abort) `(assume #f)]
    ['undef `(undef)]))

(define (parse-val v)
  (match v
    [`(union ,gvs ...) (parse-union gvs)]
    [`(term_int ,t) (call-with-values (λ () (parse-term 'int t)) (λ (a _) a))]
    [`(term_bool ,t) (call-with-values (λ () (parse-term 'bool t)) (λ (a _) a))]
    [`(list ,xs ...) (parse-list xs)]
    [`(clos ,x ,e (list ,env ...)) (closure values
                                            (parse-var x)
                                            (parse-ast e)
                                            (parse-list env))]))

(define (parse v)
  (match v
    ['none (values (none) 0)]
    [`(halt ,state)
     (define-values [val stat] (parse-state state))
     (values (halt val) stat)]
    [`(ans ,state ,v)
     (define-values [val stat] (parse-state state))
     (values (ans val (parse-val v)) stat)]))
