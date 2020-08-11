#lang rosette

; Custom serialization routines to support a generic interface for serializing objects.
; We need this since:
; - places require serialized objects to pass to/from them and it's our only method for parallelism
; - rosette doesn't allow for prefab structs so we need something else.
; - the built-in serialization:
;     * plays badly with rosette, have to implement some extremely tricky macros.
;     * is trying to support a lot of features we don't need (and is thus confusing to use)
;     * bakes (absolute) module paths into the serialized data, making it non-portable.
; This implementation tries to keep it pretty simple.
; Rather than using struct properties, it just uses a dictionary mapping struct names to pairs of serialization/deserialization functions.
; Also definitely doesn't support cycles. We don't need that, however.

; Maybe should not override the built-in functions... but there isn't a better name

(provide
  serialize
  deserialize
  register-serializable-struct
  serializable-struct
  standard-struct
  serialize-to-file
  deserialize-from-file)

(require
  "log.rkt"
  "collection.rkt")

; vector? -> symbol?
(define (struct-name vec-contents)
  ; name has a "struct:" on the front so chop that off
  (string->symbol (substring (symbol->string (vector-ref vec-contents 0)) 7)))

(define serialization-table (make-hash))

(define (atomic-type? v)
  (or
    (boolean? v)
    (number? v)
    (string? v)
    (symbol? v)))

(define (serialize val)
  (cond
   [(atomic-type? val) `(lit ,val)]
   [(list? val) `(lst ,(map serialize val))]
   [(void? val) `(void)]
   [(pair? val) `(pr ,(cons (serialize (car val)) (serialize (cdr val))))]
   [(vector? val) `(vec ,(vector-map serialize val))]
   [(and (hash? val) (hash-eq? val)) `(hsh ,(map serialize (hash->list val)))]
   [(digraph? val) 
    (unless (dg-identity-node-key? val)
      (error "cannot serialize graph with custom node key function"))
    `(gph ,(serialize-digraph serialize serialize val))]
   [(path? val) `(pth ,(path->string val))]
   [(struct? val)
    (define contents (struct->vector val))
    (define key (struct-name contents))
    (define fields (cdr (vector->list contents)))
    (unless (hash-has-key? serialization-table key)
      (error (format "no entry for ~a in serialization table!" key)))
    `(str ,key ,(map serialize fields))]
   [else (error (format "unable to serialize value ~a" val))]))

(define (deserialize val)
  (match val
   [`(lit ,val) val]
   [`(lst ,val) (map deserialize val)]
   [`(void) (void)]
   [`(pr ,val) (cons (deserialize (car val)) (deserialize (cdr val)))]
   [`(vec ,val) (vector-map deserialize val)]
   [`(hsh ,assocs) (make-immutable-hasheq (map deserialize assocs))]
   [`(gph ,val) (deserialize-digraph identity deserialize deserialize val)]
   [`(pth ,val) (string->path val)]
   [`(str ,key ,val)
    (match (hash-ref serialization-table key #f)
     [#f (error (format "no entry for ~a in serialization table!" key))]
     [ctor (apply ctor (map deserialize val))])]
   [_ (error (format "unable to deserialize type ~s" val))]))

(define (register-serializable-struct name ctor)
  (hash-set! serialization-table name ctor))

; defines a struct with default serialization/deserailization behavior.
(define-syntax (serializable-struct stx)
  (syntax-case stx ()
   [(_ name (fields ...) options ...)
    #'(begin
        (struct name (fields ...) options ...)
        (register-serializable-struct 'name name))]
   [(_ name supertype (fields ...) options ...)
    #'(begin
        (struct name supertype (fields ...) options ...)
        (register-serializable-struct 'name name))]))

; defines a transparent, serializable struct. should be used by almost everything
(define-syntax (standard-struct stx)
  (syntax-case stx ()
   [(_ name (fields ...) options ...)
    #'(serializable-struct name (fields ...) #:transparent options ...)]
   [(_ name supertype (fields ...) options ...)
    #'(serializable-struct name supertype (fields ...) #:transparent options ...)]))

; shorthand for (write-to-file fname (serialize obj))
(define (serialize-to-file fname obj)
  (write-to-file fname (serialize obj)))

(define (deserialize-from-file fname)
  (deserialize (read-from-file fname)))

