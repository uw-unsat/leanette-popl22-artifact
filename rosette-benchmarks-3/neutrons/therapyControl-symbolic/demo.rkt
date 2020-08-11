#lang rosette
(require "properties.rkt")
(require "explanations.rkt")

; (define cex (verify (watchDogProp)))
; (define cex (verify (couchInterlockProp)))
; (define cex (verify (externalMotionTolerancesProp)))
; (define cex (verify (leafTolerancesProp 0)))
(define cex (verify (filterWedgeProp)))
(cond
  [(unsat? cex) (printf "everything is ok!\n") (exit 0)]
  [#t (printf "counterexample:\n~a" (explain-counterexample cex)) (exit 1)])
