#lang racket

;; Lean should produce an answer since its partial evaluator
;; is not strong enough to reduce (* 0 s) to 0, while Rosette
;; should halt since it's able to reduce (* 0 s) to 0.
;; However, they are still equivalent logically and should
;; pass the differential testing.

;; (if (zero? (* 0 s))
;;     (assert #f)
;;     #t)

(provide expr env verification-expectation)

(define expr
  '(let0 0 #;0 (datum (op.lang.datum.int 0))
         (let0 1 #;(* 0 s) (app * 0 1)
               (let0 1 #;(= 0 (* 0 s)) (app = 0 1)
                     (if0 1
                          (make-error)
                          #t)))))

(define env '(int int))

(define verification-expectation #f)
