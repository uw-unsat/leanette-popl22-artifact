#lang racket
(require rosette)
(provide get-symb symb-name reset)

; This module helps us support lazy variable declaration and counterexample
; explanation using Rosette. Its job is to maintain a bidirectional mapping
; from symbolic variables to names.
;
; (get-symb name type)
;   --> lookup (or create) a new symbolic value with the given [name] and
;       Rosette [type] (e.g. boolean?)
;
; (symb-name v)
;   --> given a symbolic value [v] returned by get-symb, return the name it was
;       created with
;
; (reset)
;   --> clear all variable-name mappings

(define ftable (make-hash)) ; maps name->var
(define rtable (make-hash)) ; maps var->name

(define (reset)
  (set! ftable (make-hash))
  (set! rtable (make-hash)))

(define (fresh-symbolic type)
  (define-symbolic* v type)
  v)

(define (new-named-symb name type)
  (define v (fresh-symbolic type))
  (hash-set! rtable v name)
  v)

(define (get-symb name type)
  (hash-ref! ftable name (thunk (new-named-symb name type))))

(define (symb-name v)
  (hash-ref rtable v))
