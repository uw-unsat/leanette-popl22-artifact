#lang racket

(require "db.rkt")
(require "env.rkt")
(require (only-in rosette
  constant?
  bv bv?
  bitvector-size
  bitvector->integer))

(db-init-concrete)

(define (ppval v)
  (cond
    [(constant? v)  (printf "symbolic[~a]" (symb-name v))]
    [(vector? v)    (for ([x v]) (print x) (printf " "))]
    [(bv? v)        (printf "~a" (bitvector->integer v))]
    [#t             (print v)]))

(define (fields-to-show r)
  (let ([rt (record-type r)])
    (cond
      [(equal? rt "calc")     (list "A" "B" "C" "D" "E" "F" "G" "H" "I" "J" "K" "L" "VAL")]
      [(equal? rt "calcout")  (list "VAL")]
      [(equal? rt "acalcout") (list "VAL")]
      [(equal? rt "scalcout") (list "VAL")]
      [(equal? rt "bi")       (list "VAL")]
      [(equal? rt "bo")       (list "VAL")]
      [(equal? rt "ai")       (list "VAL")]
      [(equal? rt "ao")       (list "VAL")]
      [#t (list)])))

(define (show-fields r)
  (printf "fields:\n")
  (for ([f (fields-to-show r)])
    (printf "  ~a: " f)
    (ppval (get-field r f))
    (printf "\n"))
  (printf "end fields\n"))

(define (parse-value r f v)
  ; TODO: non-numeric types?
  (bv (string->number v) (bitvector-size (field-type r f))))

(define (interp line)
  (cond
    [(regexp-match? #rx"^dbgf" line)
      (match
        (regexp-match #rx"dbgf\\(\"(.*)\\.(.*)\"\\)" line)
        [(list _ r f) (ppval (get-field r f)) (printf "\n")])]
    [(regexp-match? #rx"^dbpf" line)
      (match
        (regexp-match #rx"dbpf\\(\"(.*)\\.(.*)\",.*\"(.*)\"\\)" line)
        [(list _ r f v) (set-field r f (parse-value r f v))])]
    [(regexp-match? #rx"^dbtr" line)
      (match
        (regexp-match #rx"dbtr\\(\"(.*)\"\\)" line)
        [(list _ r) (process r) (show-fields r)])]))

(define (start-processing r)
  (printf "Begin processing: '~a' of type '~a'\n" r (record-type r)))

(define (end-processing r)
  (printf "End processing: '~a' of type '~a'\n" r (record-type r))
  (show-fields r))

(set-start-processing-hook! start-processing)
(set-end-processing-hook! end-processing)

(for ([line (in-port read-line)])
  (interp line))
