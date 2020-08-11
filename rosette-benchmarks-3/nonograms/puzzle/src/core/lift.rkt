#lang rosette/safe

; some missing lifted things

(provide
 symbol?
 empty
 range/s
 build-list/s
 make-list/s
 slice
 slice*
 mapi
 foreachi
 filteri
 filter-mapi
 append-mapi
 &&map
 &&mapi
 lormap
 lormapi
 ormapi
 filter-max
 vector-andmap
 vector-ormap
 filter-map-with-arg
 list->immv
 sequential-pairs)

(require
  rosette/lib/lift
  rosette/lib/match
  (only-in racket [symbol? racket/symbol?]))

(define-lift symbol? [any/c racket/symbol?])

(define empty '())

(define (range/s s e)
  (if (>= s e)
      '()
      (cons s (range/s (add1 s) e))))

(define (build-list/s n f)
  (map f (range/s 0 n)))

(define (make-list/s n v)
  (map (λ (_) v) (range/s 0 n)))

(define (slice lst start end)
  (take (drop lst start) (- end start)))

(define (slice* lst range)
  (slice lst (car range) (cdr range)))

(define (mapi f l)
  (for/all ([l l])
    (map f (range/s 0 (length l)) l)))

(define (foreachi f l)
  (for/all ([l l])
    (for-each f (range/s 0 (length l)) l)))

(define (filteri f l)
  (map cdr
    (filter-map
      (λ (i x) (and (f i x) (cons 0 x)))
      (range/s 0 (length l)) l)))

(define (filter-mapi f l)
  (filter-map
    f
    (range/s 0 (length l)) l))

(define (append-mapi f l)
  (for/all ([l l])
    (append-map f (range/s 0 (length l)) l)))

(define-syntax-rule (&&map f lst ...) (apply && (map f lst ...)))
(define (&&mapi f lst) (for/all ([lst lst]) (apply && (map f (range/s 0 (length lst)) lst))))
; can't figure out how to use ||map without the reader OOMing the machine...
(define (lormap f lst) (apply || (map f lst)))
(define (lormapi f lst) (for/all ([lst lst]) (apply || (map f (range/s 0 (length lst)) lst))))

(define (ormapi f lst)
  (ormap f (range/s 0 (length lst)) lst))

(define (filter-max f lst)
  (define scores (map f lst))
  (define top (apply max scores))
  (filter-map (λ (x s) (and (= s top) x)) lst scores))

(define (vector-andmap f v)
  (andmap f (vector->list v)))

(define (vector-ormap f v)
  (ormap f (vector->list v)))

(define (filter-map-with-arg f lst)
  (filter-map
    (λ (x)
      (define r (f x))
      (and r (cons x r)))
    lst))

(define (list->immv lst) (vector->immutable-vector (list->vector lst)))

; 'a list? -> ('a * 'a) list
(define (sequential-pairs lst)
  (define (rec prev next)
    (match next
     ['() empty]
     [(cons head tail)
      (cons (cons prev head) (rec head tail))]))
  (cond
   [(< (length lst) 2) empty]
   [else (rec (car lst) (cdr lst))]))

