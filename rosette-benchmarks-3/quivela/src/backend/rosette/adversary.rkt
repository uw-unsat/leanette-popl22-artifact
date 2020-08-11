#lang rosette

(require rackunit)
(require "value.rkt" "lang.rkt" "print.rkt")
(provide adversary adversary? adversary-history adversary-replay
         replay-all-adversaries copy-all-adversaries check-adversary-replays
         adversary->history-string)

(struct adversary ([history #:mutable]) #:transparent
  #:property prop:procedure
  (lambda (self . rest)
    (define val (??Value 0 0 #f))
    (set-adversary-history! self (append (adversary-history self) (list (cons rest val))))
    val))
(struct adversary-replay adversary (adversary [idx #:mutable]) #:transparent
  #:property prop:procedure
  (lambda (self . rest)
    (define idx (adversary-replay-idx self))
    (match-define (list ret idx* history*)
      (for/all ([history (adversary-history (adversary-replay-adversary self))])
        (if (and (not (null? history)) (> idx -1) (equal? (car (list-ref history idx)) rest))
            (list (cdr (list-ref history idx)) (add1 idx) (append (adversary-history self) (list (cons rest (cdr (list-ref history idx))))))
            (let ()
              (define val (??Value 0 0 #f))
              (list val -1 (append (adversary-history self) (list (cons rest val))))))))
    (set-adversary-replay-idx! self idx*)
    (set-adversary-history! self history*)
    ret))


(define (replay-all-adversaries ctx)
  (define mtds*
    (for/list ([addr/mtd (Context-methods ctx)])
      (match-define (cons addr mtd) addr/mtd)
      (if (adversary? mtd)
          (cons addr (adversary-replay '() mtd 0))
          (cons addr mtd))))
  (Context-with-methods ctx mtds*))

; match up the adversaries in ctx1 and ctx2,
; replace those in ctx1 with copies,
; then replace those in ctx2 with replays of those copies
(define (copy-all-adversaries ctx1 ctx2)
  (define old->new (make-hasheq))
  (define ctx1-mtds (for/list ([addr/mtd (Context-methods ctx1)])
                      (match-define (cons addr mtd) addr/mtd)
                      (if (adversary? mtd)
                          (let ([adv* (adversary (adversary-history mtd))])
                            (hash-set! old->new mtd adv*)
                            (cons addr adv*))
                          addr/mtd)))
  (define ctx2-mtds (for/list ([addr/mtd (Context-methods ctx2)])
                      (match-define (cons addr mtd) addr/mtd)
                      (if (adversary-replay? mtd)
                          (let ([adv* (hash-ref old->new (adversary-replay-adversary mtd))])
                            (cons addr (adversary-replay (adversary-history mtd) adv* (adversary-replay-idx mtd))))
                          addr/mtd)))
  (values (Context-with-methods ctx1 ctx1-mtds)
          (Context-with-methods ctx2 ctx2-mtds)))

; check that all adversaries were replayed fully (i.e. did not diverge)
(define (check-adversary-replays ctx2)
  (apply &&
    (for/list ([addr/mtd (Context-methods ctx2)]
               #:when (adversary-replay? (cdr addr/mtd)))
      (equal? (adversary-replay-idx (cdr addr/mtd))
              (length (adversary-history (adversary-replay-adversary (cdr addr/mtd))))))))

(define (adversary->history-string adv)
  (define h (adversary-history adv))
  (string-join (for/list ([call/ret h])
                 (match-define (cons call ret) call/ret)
                 (match-define (cons name rest) call)
                 (define args (string-join (map value-to-string rest) ", "))
                 (format "~a(~a) = ~a" name args (value-to-string ret)))
               "; "))

(module+ test
  (define X (adversary '()))
  (define old1 (X 5))
  (define old2 (X 6))
  (define old3 (X 7))
  (define old4 (X 8))
  ; replay in the same order
  (define X1 (adversary-replay X 0))
  (check-true (unsat? (verify (assert (equal? (X1 5) old1)))))
  (check-true (unsat? (verify (assert (equal? (X1 6) old2)))))
  (check-true (unsat? (verify (assert (equal? (X1 7) old3)))))
  (check-true (unsat? (verify (assert (equal? (X1 8) old4)))))
  ; replay in different order -- once we diverge we're tained forever
  (define X2 (adversary-replay X 0))
  (check-true  (unsat? (verify (assert (equal? (X2 5) old1)))))
  (check-false (unsat? (verify (assert (equal? (X2 7) old2)))))
  (check-false (unsat? (verify (assert (equal? (X2 6) old3)))))
  (check-false (unsat? (verify (assert (equal? (X2 8) old4)))))

  ; test control flow
  (define Y (adversary '()))
  (define-symbolic* cond boolean?)
  (define ret1
    (if cond (Y 10) (Y 20)))
  (define ret2 (Y 30))
  ; replay with the same condition should be unsat
  (define Y1 (adversary-replay Y 0))
  (define new1
    (if cond (Y1 10) (Y1 20)))
  (define new2 (Y1 30))
  (check-true (unsat? (verify (assert (equal? ret1 new1)))))
  (check-true (unsat? (verify (assert (equal? ret2 new2)))))
  ; replay with the condition inverted should be sat
  (define Y2 (adversary-replay Y 0))
  (define new3
    (if (! cond) (Y2 10) (Y2 20)))
  (define new4 (Y2 30))
  (check-false (unsat? (verify (assert (equal? ret1 new3)))))
  (check-false (unsat? (verify (assert (equal? ret2 new4)))))
  )
  