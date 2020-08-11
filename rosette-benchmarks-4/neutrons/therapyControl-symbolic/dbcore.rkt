#lang rosette

(require "env.rkt")
(provide (except-out (all-defined-out) find-box))

(struct Database (is-concrete data) #:mutable #:transparent)

(define (new-symbolic-database)
  (Database #f (make-hash)))

(define (new-concrete-database)
  (Database #t (make-hash)))

(define (make-concrete-value type)
  (match type
    [(vector n t)   (build-vector n (lambda (i) (make-concrete-value t)))]
    [_ (cond
      [(bitvector? type)     (bv 0 (bitvector-size type))]
      [(eq? boolean? type)   #f]
      [#t (eprintf "Unknown type: ~s\n" type)])]))

(define (make-symbolic-value name type)
  (match type
    [(vector n t)   (build-vector n (lambda (i) (make-symbolic-value (string-append name "[" (number->string i) "]") t)))]
    [_              (get-symb name type)]))

(define (find-box db r f type)
  (let ([name (string-append r "." f)])
    (hash-ref! (Database-data db) name
      (thunk (box (if (or (Database-is-concrete db) (equal? f "PACT"))
        (make-concrete-value type)
        (make-symbolic-value name type)))))))

(define (db-get db r f type)
  (unbox (find-box db r f type)))

(define (db-put! db r f type value)
  (set-box! (find-box db r f type) value))
