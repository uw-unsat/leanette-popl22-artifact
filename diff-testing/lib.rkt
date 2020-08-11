#lang rosette

(provide make-symbolic-var
         reset-store!
         with-env-size
         lam
         link
         (struct-out ans)
         (struct-out state)
         (struct-out none)
         (struct-out closure)
         (struct-out undef)
         (struct-out halt))

(require syntax/parse/define
         racket/stxparam
         (for-syntax racket/syntax))

(define all-symbolic-vars (make-hash))

(define (make-symbolic-var type x)
  (match type
    ['int (hash-ref! all-symbolic-vars x
                     (λ ()
                       (define-symbolic* x integer?)
                       x))]
    ['bool (hash-ref! all-symbolic-vars x
                      (λ ()
                        (define-symbolic* x boolean?)
                        x))]))

(struct ans (state v) #:transparent)
(struct state (assumes asserts) #:transparent)
(struct none () #:transparent)
(struct closure (f x e env) #:transparent
  #:property prop:procedure (struct-field-index f)
  #:methods gen:equal+hash
  [(define equal-proc (λ (a b recur)
                        (&& (equal? (closure-x a) (closure-x b))
                            (equal? (closure-e a) (closure-e b))
                            (equal? (closure-env a) (closure-env b)))))
   ;; we are not doing hashing
   (define hash-proc  (λ (a recur) 0))
   (define hash2-proc (λ (a recur) 0))])

(struct undef () #:transparent)
(struct halt (state) #:transparent)

(define (reset-store!) (hash-clear! all-symbolic-vars))

(define-syntax-parse-rule (lam x:id e)
  #:with (xs ...) (for/list ([x (in-range (syntax-parameter-value #'current-env-size))])
                    (format-id this-syntax "x~a" x))
  (let ()
    (closure (λ (x) e)
             (quote x)
             (quote e)
             (list xs ...))))

(define (link x xs)
  (assert (list? xs))
  (cons x xs))

(define-syntax-parameter current-env-size #f)

(define-syntax-parse-rule (with-env-size n:nat body ...)
  (syntax-parameterize ([current-env-size n])
    body ...))
