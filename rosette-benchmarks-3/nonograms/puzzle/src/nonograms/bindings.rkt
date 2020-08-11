#lang rosette/safe

(provide
  gaps-of-line
  blocks-of-line
  cell-indices-of-line)

(require
  (only-in racket error)
  "../core/core.rkt"
  "symbolic.rkt"
  "rules.rkt")

; (cell? -> bool?), line? -> (listof segment?)
(define (segments-of-concrete-line partition-fn ctx)
  (when (symbolic? ctx) (error "only concrete lines supported"))
  (define cells (line-cells ctx))
  (define (foldfn i c acc)
    (define segs (first acc))
    (define last-start (second acc))
    (define last-len (third acc))
    (cond
     [(partition-fn c)
      (list segs last-start (add1 last-len))]
     [(> last-len 0)
      (list (cons (segment last-start (+ last-len last-start) #t) segs) (add1 i) 0)]
     [else (list segs (add1 i) 0)]))
  (define res (foldl foldfn (list '() 0 0) (range/s 0 (add1 (line-length ctx))) (append cells (list #f))))
  (reverse (first res)))

(define (segments-of-symbolic-line partition-fn ctx)
  (define len (line-length ctx))
  (define max-segments (quotient (add1 len) 2))
  (define cells (line-cells ctx))
  (define-values (segments seg-count) (symbolic-segments ctx max-segments))
  (for-each
    (λ (i c)
      (define (in-seg? s)
        (&& (segment-used? s) (<= (segment-start s) i) (< i (segment-end s))))
      (define in-any? (lormap in-seg? segments))
      (assert (<=> (partition-fn c) in-any?)))
    (range/s 0 len)
    cells)
  (take segments seg-count))

(define (segments-of-line partition-fn ctx #:symbolic? [symb? 'detect])
  (cond
   [(or (equal? symb? #t) (and (equal? symb? 'detect) (symbolic? ctx)))
    (segments-of-symbolic-line partition-fn ctx)]
   [else
    (segments-of-concrete-line partition-fn ctx)]))

; line? -> (listof segment?)
(define (gaps-of-line ctx #:symbolic? [s? 'detect])
  (define (in-gap? c)
    (|| (true-cell? c) (empty-cell? c)))
  (segments-of-line in-gap? ctx #:symbolic? s?))

; line? -> (listof segment?)
(define (blocks-of-line ctx #:symbolic? [s? 'detect])
  (segments-of-line true-cell? ctx #:symbolic? s?))

; line? -> (listof ???)
(define (cell-indices-of-line ctx)
  (make-list/s (line-length ctx) 0))

