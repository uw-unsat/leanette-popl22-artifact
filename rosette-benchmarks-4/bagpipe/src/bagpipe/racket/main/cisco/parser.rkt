#lang racket

(require srfi/13)
(require "../util/util.rkt")

(provide cisco->sexp)

(define cisco-sexp-path (bagpipe-path "src/bagpipe/hs/dist/build/cisco-sexp/cisco-sexp"))

(define (cisco->sexp files)
  (define-values (process out in err)
    (apply subprocess #f #f #f cisco-sexp-path files))
  (with-handlers ([exn:break? (lambda (e) 
                                (subprocess-kill process #t)
                                (error 'solve "user break"))])
    (read out)))

