#lang rosette

(provide bounded! **BOUND** define/rec current-bound!)
(require (only-in racket string-append symbol->string))

(define **BOUND** 10)

(define (current-bound! [n 0])
    (if (= n 0)
        **BOUND**
        (set! **BOUND** n)))

(define-syntax (bounded! stx)
    (syntax-case stx ()
        [(_ fun n)
        (datum->syntax
            stx
            (syntax->datum
                #`((lambda()
                    (begin
                      (define temp fun)
                      (define counter 0)
                      (set! fun
                          (lambda (f . rest)
                              (begin
                                  (assert (< counter n) "Recursion!")
                                  (set! counter (+ counter 1))
                                  (define ANS (apply temp (cons f rest)))
                                  (set! counter (- counter 1))
                                  ANS)))))))
            stx)]))

(define-syntax (define/rec stx)
    (syntax-case stx ()
        [(_ (name args ...) body ...)
        #`(define name
            ((lambda ()
                (define counter 0)
                (define (temp args ...)
                    body ...)
                (lambda (f . rest)
                    (begin
                        (if (> counter **BOUND**)
                            'nothing
                            (begin
                                (set! counter (+ counter 1))
                                (define ANS (apply temp (cons f rest)))
                                (set! counter (- counter 1))
                                ANS)))))))]))

(define/rec (f n m)
    (displayln m)
    (if (< n 2) 1
        (* n (f (- n 1) m))))
