#lang racket

;; Lean should loop infinitely on this program since its partial evaluator
;; is not strong enough to reduce (* 0 s) to 0, while Rosette
;; should not get stuck since it's able to reduce (* 0 s) to 0.

;; (if (zero? (* 0 s))
;;     #t
;;     (infinite-loop))

(provide expr env verification-expectation)

(define expr
  `(let0 0 #;0 (datum (op.lang.datum.int 0))
         (let0 1 #;(* 0 s) (app * 0 1)
               (let0 1 #;(= 0 (* 0 s)) (app = 0 1)
                     (if0 1
                          #t
                          (let0 0 #;little-omega (λ 0 (call 0 0))
                                (call 0 0)))))))


(define env '(int int))

(define verification-expectation #t)
