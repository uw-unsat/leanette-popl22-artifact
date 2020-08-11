#lang racket

(provide (struct-out metric)
         (struct-out rosette-metric)
         (struct-out lean-metric)
         calc-size)

(struct metric [path round size rosette lean result] #:mutable #:prefab)
(struct rosette-metric [time trivial? size] #:mutable #:prefab)
(struct lean-metric [time trivial? size] #:mutable #:prefab)

(define (calc-size x)
  (match x
    [`(let0 ,x ,v ,b) (+ 1 (calc-size v) (calc-size b))]
    [`(if0 ,c ,t ,e) (+ 1 (calc-size t) (calc-size e))]
    [`(app ,_ ...) 1]
    [`(call ,_ ,_) 1]
    [`(var ,_) 1]
    [`(datum ,_) 1]
    [(or #t #f) 1]
    [`(λ ,x ,b) (+ 1 (calc-size b))]
    [`(make-error) 1]
    [`(make-abort) 1]
    ['undef 1]))
