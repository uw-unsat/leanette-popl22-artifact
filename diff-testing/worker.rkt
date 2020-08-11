#lang racket

(provide place-main)
(require data/queue
         (prefix-in rosette-backend: "rosette-backend.rkt")
         (prefix-in rosette: rosette)
         "lib.rkt"
         "utils.rkt")

(define cnt 0)
(define main-thread (current-thread))

(define (print-lean-expr v)
  (match v
    [`(let0 ,x ,v ,b)
     (string-append "(let0 " (~a x) " " (print-lean-expr v) " " (print-lean-expr b) ")")]
    [`(datum (op.lang.datum.int ,z)) (string-append "(datum (op.lang.datum.int "
                                                    (cond
                                                      [(negative? z) (format "(~a)" z)]
                                                      [else (~a z)])
                                                    "))")]
    [`(if0 ,c ,t ,e)
     (string-append "(if0 "
                    (~a c)
                    " "
                    (print-lean-expr t)
                    " "
                    (print-lean-expr e)
                    ")")]
    [`(app ,o ,xs ...)
     (string-append "(app "
                    (match o
                      ['< "(op.lang.op.int_2 op.lang.op_int_2.lt)"]
                      ['= "(op.lang.op.int_2 op.lang.op_int_2.eq)"]
                      ['+ "(op.lang.op.int_2 op.lang.op_int_2.add)"]
                      ['* "(op.lang.op.int_2 op.lang.op_int_2.mul)"]
                      ['first "(op.lang.op.list_proj op.lang.op_list_proj.first)"]
                      ['rest "(op.lang.op.list_proj op.lang.op_list_proj.rest)"]
                      ['make-null "op.lang.op.list_null"]
                      ['link "op.lang.op.list_cons"]
                      ['null? "op.lang.op.list_is_null"])
                    " ["
                    (string-join (map ~a xs) ", ")
                    "]"
                    ")")]
    [`(call ,f ,a) (format "(call ~a ~a)" f a)]
    [`(var ,x) (format "(var ~a)" x)]
    [#t "(bool tt)"]
    [#f "(bool ff)"]
    [`(λ ,x ,b) (string-append "(lam " (~a x) " " (print-lean-expr b) ")")]
    [`(make-error) "error"]
    [`(make-abort) "abort"]
    ['undef "(datum op.lang.datum.undef)"]))

(define (do-eval r)
  (cond
    [(ans? r)
     (rosette:if (rosette:! (state-asserts (ans-state r)))
                 (halt (state #t #f))
                 (rosette:if (rosette:! (state-assumes (ans-state r)))
                             (halt (state #f #t))
                             (ans-v r)))]
    [else r]))

(define (collect-rosette-stats t)
  (define seen (mutable-seteq))
  (let loop ([t t])
    (cond
      [(set-member? seen t) 0]
      [else
       (set-add! seen t)
       (match t
         [(rosette:expression _ children ...)
          (+ 1 (for/sum ([child children]) (loop child)))]
         [_ 1])])))

(define q (make-queue))

(define current-expr (make-parameter #f))
(define current-env (make-parameter #f))
(define current-verification-expectation (make-parameter #f))
(define current-mutation-depth (make-parameter #f))

(define lines '())

(define (report line)
  (set! lines (cons line lines)))

(define (place-main ch)
  (match-define `(init ,place-id
                       ,the-seed
                       ,fuel
                       ,rosette-verify?
                       ,max-mutation-depth
                       ,max-mutation-repeat
                       ,mutate-ignore-error?
                       ,mutator-paths
                       ,timeout)
    (place-channel-get ch))

  (define mutators
    (for/list ([path mutator-paths])
      (dynamic-require path 'mutate)))

  (define (do-gen:rosette rosette-path)
    (define rosette-code
      `((provide result)
        (require "../lib.rkt")

        (define (make-null) '())

        ,@(for/list ([e (current-env)] [i (in-naturals)])
            `(define ,(string->symbol (format "x~a" i))
               (make-symbolic-var ',e ,i)))

        ,(cond
           [rosette-verify?
            `(define result (verify ,(rosette-backend:parse-ast (current-expr))))]
           [else
            `(define result
               (let* ([result (with-env-size ,(length (current-env)) (with-vc ,(rosette-backend:parse-ast (current-expr))))]
                      [the-state (result-state result)]
                      [the-state (state (vc-assumes the-state) (vc-asserts the-state))])
                 (cond
                   [(normal? result) (ans the-state (result-value result))]
                   [else (halt the-state)])))])))

    (report `(rosette-code ,(format-rosette-code rosette-code)))

    (with-output-to-file rosette-path
      #:exists 'replace
      (λ () (displayln (format-rosette-code rosette-code)))))

  (define (do-gen:lean lean-path)
    (define (gen-lean-env)
      (string-append
       "["
       (string-join
        (for/list ([x (current-env)] [i (in-naturals)])
          (format "(val.atom (val_atom.term (term.var (var.mk type.~a ~a))))" x i))
        ", ")
       "]"))

    (define lean-code (string-append
                       "
import ..sym_factory.sym_factory
import ..generation.main
import ..generation.printer
import ..interp.sym.defs
import ..op.sym

open lang.exp
open op.sym

def input_exp : lang.exp op.lang.datum op.lang.op
  := " (print-lean-expr (current-expr)) "

#eval result.to_str $
  (interp.interpS sym_factory.sym_factory " fuel "
    input_exp
    " (gen-lean-env) " initial_state) "))

    (report `(lean-code ,lean-code))

    (with-output-to-file lean-path
      #:exists 'replace
      (λ () (displayln lean-code))))


  (define (mutate r ok?)
    (when (and (positive? (current-mutation-depth))
               (if ok? #t mutate-ignore-error?))
      (unless (empty? mutators)
        (define iterations (if (= (current-mutation-depth) max-mutation-depth)
                               max-mutation-repeat
                               1))
        (for ([i iterations])
          ((choose mutators)
           r (current-expr) (current-env)
           (λ (new-expr new-env)
             (enqueue! q (list new-expr
                               new-env
                               'none
                               (sub1 (current-mutation-depth))))))))))

  (define (do-gen)
    (when the-seed (random-seed the-seed))
    (reset-store!)
    (rosette:clear-state!)
    (define rosette-path (format "workspace/prog-~a-~a.rkt" place-id cnt))
    (set! cnt (add1 cnt))
    (cond
      [rosette-verify?
       (report `(verification-expectation ,(current-verification-expectation)))
       (match (current-verification-expectation)
         [(or #t #f)
          ;; we assume verification expectation != none implies the program terminates
          (do-gen:rosette rosette-path)
          (match-define-values [(list sol) _ rosette-time _]
            (time-apply (λ () (dynamic-require rosette-path 'result)) '()))
          (delete-file rosette-path)
          (report `(rosette-result ,(pretty-format sol) ,rosette-time))
          (when sol
            (cond
              [(or (and (rosette:unsat? sol) (current-verification-expectation))
                   (and (rosette:sat? sol) (not (current-verification-expectation))))
               (report 'verification-matched)]
              [else
               (report 'verification-unmatched)]))]
         [_ (void)])]
      [else
       ;; Rosette
       (match-define-values [(list rosette-terminate?) _ rosette-time _]
         (let ()
           (do-gen:rosette rosette-path)
           (define thd
             (thread (λ () (thread-send main-thread (dynamic-require rosette-path 'result)))))
           (begin0 (time-apply (λ () (sync/timeout/enable-break timeout thd)) '())
             (kill-thread thd)
             (delete-file rosette-path))))

       (cond
         [rosette-terminate?
          (define result-from-racket (thread-receive))
          (report `(rosette-result ,(pretty-format result-from-racket) ,rosette-time))
          (define stat-from-racket
            (match result-from-racket
              [(or (halt (state assumes asserts))
                   (ans (state assumes asserts) _))
               (+ (collect-rosette-stats assumes)
                  (collect-rosette-stats asserts))]))
          (report `(rosette-state
                    ,(match result-from-racket
                       [(or (halt (state assumes asserts))
                            (ans (state assumes asserts) _))
                        (and (boolean? assumes) (boolean? asserts)
                             (= 2 stat-from-racket))])
                    ,stat-from-racket))

          ;; Lean
          (define-values (in out) (make-pipe))
          (match-define-values [(list lean-terminate?) _ lean-time _]
            (parameterize ([current-directory "../lean"])
              (define lean-path (format "src/workspace/load-~a-~a.lean" place-id cnt))
              (set! cnt (add1 cnt))
              (do-gen:lean lean-path)
              (define thd
                (thread
                 (λ ()
                   (match-define (list _ _ _ _ proc)
                     (process*/ports out (current-input-port) 'stdout
                                     (find-executable-path "lean") lean-path))
                   (thread-send main-thread proc)
                   (proc 'wait))))
              (begin0 (time-apply (λ () (sync/timeout/enable-break timeout thd)) '())
                (delete-file lean-path)
                ((thread-receive) 'kill)
                (kill-thread thd))))

          (cond
            [lean-terminate?
             (close-output-port out)
             (define read-result (port->string in))
             (match read-result
               [(pregexp #px"\"(.*?)\"" (list _ read-result))
                (define v (read (open-input-string read-result)))
                (define-values [result-from-lean stat-from-lean]
                  (rosette-backend:parse v))
                (report `(lean-result ,(pretty-format result-from-lean) ,lean-time))
                (report `(lean-state
                          ,(match result-from-lean
                             [(none) #t]
                             [(or (halt (state assumes asserts))
                                  (ans (state assumes asserts) _))
                              (and (boolean? assumes) (boolean? asserts)
                                   (= stat-from-lean 2))])
                          ,stat-from-lean))

                ;; Diff
                (cond
                  [(none? result-from-lean)
                   (mutate #f #f)]
                  [else
                   (define sol
                     (rosette:verify
                      (rosette:assert
                       (rosette:equal? (do-eval result-from-lean)
                                       (do-eval result-from-racket)))))
                   (cond
                     [(rosette:unsat? sol)
                      (report 'agree)
                      (mutate result-from-racket #t)]
                     [else
                      (report `(disagree
                                ,(pretty-format sol)
                                ,(pretty-format (rosette:evaluate (do-eval result-from-lean) sol))
                                ,(pretty-format (rosette:evaluate (do-eval result-from-racket) sol))))
                      (mutate #f #f)])])]
               [else (report `(fatal-error ,read-result))
                     (mutate #f #f)])]

            [else (report 'lean-timeout)
                  (mutate #f #f)])]
         [else (report 'rosette-timeout)
               (mutate #f #f)])]))

  (place-channel-put ch `(ready ,place-id))
  (let loop ()
    (match-define `(work ,prog) (place-channel-get ch))
    (enqueue! q (list (dynamic-require prog 'expr)
                      (dynamic-require prog 'env)
                      (dynamic-require prog 'verification-expectation)
                      max-mutation-depth))

    (let loop ()
      (when (non-empty-queue? q)
        (match-define (list e env ve mutation-depth) (dequeue! q))
        (parameterize ([current-expr e]
                       [current-env env]
                       [current-verification-expectation ve]
                       [current-mutation-depth mutation-depth])
          (do-gen)
          (report 'flush))
        (loop)))

    (place-channel-put ch `(ans ,prog ,(reverse lines)))
    (place-channel-put ch `(ready ,place-id))
    (set! lines '())
    (loop)))
