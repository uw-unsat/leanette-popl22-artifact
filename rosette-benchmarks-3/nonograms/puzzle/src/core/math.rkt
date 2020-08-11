#lang rosette/safe

; some math routines that are used by a bunch o modules but are quite generic.

(provide
  choices
  choices-up-to
  cartesian-product
  transpose)

(require
  (only-in racket make-vector for)
  rosette/lib/match
  "lift.rkt")

; COMBINATORICS
;-----------------------------------------------------------------------------

; list?, posint? -> (listof list?)
; returns all distinct choices of size k for lst.
(define (choices lst k)
  (cond
   [(> k (length lst)) empty]
   [else
    (match lst
     [(cons head tail)
      (append
        (map (curry cons head) (choices tail (sub1 k)))
        (choices tail k))]
     ['() (if (zero? k) (list empty) empty)])]))

; all distinct non-empty choices up to size k (1 to k inclusive)
(define (choices-up-to lst k)
  (append-map (curry choices lst) (range/s 1 (add1 k))))

; cartesian product: cons every element in front to each list in back
; equivalent to (for*/list ([x front] [l back]) (cons x l)), though the result will be backwards
(define (cp front back)
  (foldl
    (λ (x acc)
       (foldl (λ (l acc2) (cons (cons x l) acc2)) acc back))
    '()
    front))

; TODO this is... in the standard library, because of course it is.
; cartesian product of a list of lists
(define (cartesian-product lst)
  (if (ormap empty? lst)
      '()
      (foldr cp (list '()) lst)))


; LIST OPS
;-----------------------------------------------------------------------------

; 'a vector vector -> 'a vector vector
; turns an NxM vector of vectors into the MxN tranpose.
(define (transpose mtrx)
  (define n (vector-length mtrx))
  (define m (vector-length (vector-ref mtrx 0)))
  (define out (make-vector m))
  (for ([i m])
    (define in (make-vector n))
    (vector-set! out i in)
    (for ([j n])
      (vector-set! in j (vector-ref (vector-ref mtrx j) i))))
  out)

