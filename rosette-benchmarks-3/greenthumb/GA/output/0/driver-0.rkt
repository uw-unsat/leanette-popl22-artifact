#lang racket
(require (file "../../GA-parser.rkt") (file "../../GA-machine.rkt") (file "../../GA-printer.rkt") (file "../../GA-simulator-racket.rkt") (file "../../GA-simulator-rosette.rkt") (file "../../GA-validator.rkt") (file "../../GA-symbolic.rkt"))
(require rosette/solver/smt/boolector (only-in rosette current-solver))
(current-solver (boolector))
(define machine (new GA-machine% [config #f]))
(define printer (new GA-printer% [machine machine]))
(define parser (new GA-parser%))
(define simulator-racket (new GA-simulator-racket% [machine machine]))
(define simulator-rosette (new GA-simulator-rosette% [machine machine]))
(define validator (new GA-validator% [machine machine] [simulator simulator-rosette]))
(define search (new GA-symbolic% [machine machine] [printer printer] [parser parser] [validator validator] [simulator simulator-rosette] [syn-mode `linear]))
(define prefix (send parser ir-from-string "
"))
(define code (send parser ir-from-string "
0 a! !+ push !+ pop 1 b! @b over or 0 b! @b or push drop pop "))
(define postfix (send parser ir-from-string "
"))
(define encoded-prefix (send printer encode prefix))
(define encoded-code (send printer encode code))
(define encoded-postfix (send printer encode postfix))
(send search superoptimize encoded-code (send machine output-constraint '((data . 2))) "output/0/driver-0" 3600 #f #:assume (send machine constrain-stack '((<= . 65535) (<= . 65535) (<= . 65535))) #:input-file "data-iii2/inputs" #:start-prog #f #:prefix encoded-prefix #:postfix encoded-postfix)
