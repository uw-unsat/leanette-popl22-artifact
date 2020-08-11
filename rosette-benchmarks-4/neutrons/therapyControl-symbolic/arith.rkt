#lang rosette
(provide >> << bvor bvand + - * / > < >= <= = zero? abs)

; This module lets you use your favorite arithmetic operators (+, -, =, etc.)
; while mixing Rosette 2.0's bitvector types and integers.

(require (prefix-in old (only-in rosette + - * / > < >= <= = zero? abs bvor bvand)))

(define-syntax-rule (lift-2op-to-bitvectors op old bv-equivalent)
  (define (op xraw yraw)
    (for*/all ([x xraw] [y yraw])
      (cond
        [(and (bv? x) (bv? y))      (bv-equivalent x y)]
        [(and (bv? x) (integer? y)) (bv-equivalent x (integer->bitvector y (bitvector (bitvector-size (type-of x)))))]
        [(and (integer? x) (bv? y)) (bv-equivalent (integer->bitvector x (bitvector (bitvector-size (type-of y)))) y)]
        [#t (old x y)]))))

(define (to-bv w)
  (lambda (xraw)
    (for/all ([x xraw])
      (cond
        [(and (bv? x) (< (bitvector-size (type-of x)) w)) (sign-extend x (bitvector w))]
        [(and (bv? x) (> (bitvector-size (type-of x)) w)) (extract (- w 1) 0 x)]
        [(bv? x) x]
        [#t (integer->bitvector x (bitvector w))]))))

(define (bvwidth xraw)
  (for/all ([x xraw])
    (cond
      [(bv? x) (bitvector-size (type-of x))]
      [#t -1])))

(define (pick-bitwidth l)
  (foldl max -1 (map bvwidth l)))

(define-syntax-rule (lift-Nop-to-bitvectors op old bv-equivalent)
  (define (op . argsraw)
    (for/all ([args argsraw])
      (for/all ([w (pick-bitwidth argsraw)])
        (cond
          [(> w 0) (apply bv-equivalent (map (to-bv w) args))]
          [#t      (apply old args)])))))

(define (iashr x y)
  (bitvector->integer (bvashr
    (integer->bitvector x (bitvector 64))
    (integer->bitvector y (bitvector 64)))))
(define (ishl x y)
  (bitvector->integer (bvshl
    (integer->bitvector x (bitvector 64))
    (integer->bitvector y (bitvector 64)))))
(define (ior . args)
  (bitvector->integer (apply bvor (map (lambda (x) (integer->bitvector x (bitvector 64))) args))))
(define (iand . args)
  (bitvector->integer (apply bvand (map (lambda (x) (integer->bitvector x (bitvector 64))) args))))

(lift-Nop-to-bitvectors +  old+  bvadd)
(lift-Nop-to-bitvectors -  old-  bvsub)
(lift-Nop-to-bitvectors /  old/  bvsdiv)
(lift-Nop-to-bitvectors *  old*  bvmul)
(lift-Nop-to-bitvectors =  old=  equal?)
(lift-2op-to-bitvectors >  old>  bvsgt)
(lift-2op-to-bitvectors <  old<  bvslt)
(lift-2op-to-bitvectors <= old<= bvsle)
(lift-2op-to-bitvectors >= old>= bvsgt)

(lift-2op-to-bitvectors >>    iashr bvashr)
(lift-2op-to-bitvectors <<    ishl  bvshl)
(lift-Nop-to-bitvectors bvor  ior   oldbvor)
(lift-Nop-to-bitvectors bvand iand  oldbvand)

(define (bvltz x)
  (for/all ([bvx x])
    (bvslt bvx (bv 0 (bitvector-size (type-of bvx))))))

(define (abs xraw)
  (for/all ([x xraw])
    (cond
      [(bv? x) (if (bvltz x) (bvneg x) x)]
      [#t (oldabs x)])))

(define (zero? xraw)
  (for/all ([x xraw])
    (cond
      [(bv? x) (equal? x (bv 0 (bitvector-size (type-of x))))]
      [#t (oldzero? x)])))
