#lang rosette

(provide
  reset pre post examine status check freeze
  (all-from-out "db.rkt")
  (all-from-out "arith.rkt"))

(require "db.rkt")
(require "arith.rkt")
(require "explanations.rkt")

(define assumption-formula '())
(define assumptions '())
(define assertion-formula '())
(define assertions '())
(define record #f)

(define (reset)
  (set! assertions '())
  (set! assumptions '())
  (set! assertion-formula '())
  (set! assumption-formula '())
  (set! record #f))

(define (enqueue-assert e fn)
  (set! assertions (append assertions (list e)))
  (set! assertion-formula (append assertion-formula (list fn))))

(define-syntax post
  (syntax-rules ()
    ((_ e) (enqueue-assert 'e (lambda () e)))))

(define (enqueue-assume e fn)
  (set! assumptions (append assumptions (list e)))
  (set! assumption-formula (append assumption-formula (list fn))))

(define-syntax pre
  (syntax-rules ()
    ((_ e) (enqueue-assume 'e (lambda () e)))))

(define (examine r)
  (set! record r))

(define (status)
  (printf "examining: ~a\nprecondition: ~s\npostcondition: ~s\n" record assumptions assertions))

(define (eval-formula f)
  (if (empty? f) #t
    (and ((car f)) (eval-formula (cdr f)))))

(define (check)
  (define (testcase)
    (define precond (eval-formula assumption-formula))
    (if record (process record) #f)
    (define postcond (eval-formula assertion-formula))
    (assert (=> precond postcond)))
  (db-init-symbolic)
  (define cex (verify (testcase)))
  (cond
    [(unsat? cex) (printf "everything is ok!\n")]
    [#t (printf "counterexample:\n~a" (explain-counterexample cex)) cex]))

(define (freeze name)
  (printf "(define (~a)\n" name)
  (printf "  (define pre ") (write (cons 'and assumptions)) (printf ")\n")
  (if record (printf "  (process ~v)\n" record) #f)
  (printf "  (define post ") (write (cons 'and assertions)) (printf ")\n")
  (printf "  (assert (=> pre post)))\n")
  (printf "; --------------------------------------------------------------\n")
  (printf "; Paste the above definition into a file (e.g. '~a.rkt')\n" name)
  (printf "; and you can check it later using\n")
  (printf ";     $ check-symbolic path/to/symbolic/ioc ~a.rkt ~a\n" name name)
  (printf "; --------------------------------------------------------------\n"))

(reset)
