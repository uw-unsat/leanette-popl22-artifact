#lang rosette

(require (only-in racket/stxparam define-syntax-parameter syntax-parameterize)
         (only-in racket/undefined undefined)
         (for-syntax (only-in racket/syntax generate-temporary)))

(provide
 ; rosette primitives
 (except-out (all-from-out rosette) verify
     #%app if when unless cond begin set! lambda define let) ;let* let-values let*-values)  
 ; IVL primitives
 return undefined? assume stuck? raze exception?
 (rename-out [$app #%app] [$if if] [$when when] [$unless unless] [$cond cond]
             [$begin begin] [$set! set!] [$verify verify]
             [$lambda lambda] [$define define] [$let let]))


(define-syntax-parameter return (lambda (stx) #'undefined))
(define-syntax-parameter raze (lambda (stx) #'undefined))

(define (undefined? x) (eq? x undefined))
(define (stuck? x) false)
(define  exc
  (let ()
    (struct exception ())
    (exception)))
(define (exception? x) (eq? x exc))

(define-syntax-rule (unless-done expr)
  (when (undefined? return)
    expr))

(define-syntax-rule ($if test then else)
  (unless-done (if (void? test) false (if test then else))))

(define-syntax-rule ($when e ...)
  (unless-done (when e ...)))

(define-syntax-rule ($unless e ...)
  (unless-done (unless e ...)))

(define-syntax-rule ($cond e ...)
  (unless-done (cond e ...)))

(define-syntax-rule ($begin e ...)
  (unless-done (begin e ...)))

(define-syntax-rule ($let e ...)
  (unless-done (let e ...)))
    
(define-syntax ($app stx)
  (syntax-case stx ()
    [(_ proc arg ...)
     (let* ([args (syntax->list #'(arg ...))]
            [vars (map (lambda (e)
                         (and (not (keyword? (syntax->datum e)))
                              (generate-temporary 't)))
                       args)]
            [defs (filter-map (lambda (v a) (and v (list v a))) vars args)]
            [uses (map (lambda (v a) (if v v a)) vars args)])
       #`(let* ([p proc] #,@defs)
           (unless-done (let ([ret (p #,@uses)]) (if (exception? ret) (begin (raze) exc) ret)))))]))


(define-syntax-rule ($set! id expr)
  (unless-done (set! id expr)))

(define-syntax ($lambda stx)
  (syntax-case stx ()
    [(_ args body ...)
     #`(lambda args
         (let ([ret undefined])
           (syntax-parameterize
               ([return (syntax-id-rules ()
                          [(_) ($set! ret (void))]
                          [(_ expr) ($set! ret expr)]
                          [_ ret])]
                [raze (syntax-id-rules ()
                          [(_) (begin ($set! ret exc) exc)]
                          [(_ expr) (begin ($set! ret exc) exc)]
                          [_ (begin ($set! ret exc) exc)])] )

             body ...)
           ret))]))

(define-syntax ($define stx)
  (syntax-case stx ()
    [(_ (id args ...) body ...)
     #`(define id ($lambda (args ...) body ...))]
    [(_ id expr)
     #`(define id expr)]))

(define (result->solution r)
  (if (normal? r) (result-value r) (unsat)))

(define-syntax-rule ($verify #:assume pre #:guarantee post)
  (result->solution (with-vc (begin pre (verify post)))))