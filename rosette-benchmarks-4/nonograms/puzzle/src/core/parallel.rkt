#lang racket

; Functions to map a function over a list in parallel/concurrently.
; Provides two different implementations:
; 1) A truly parallel map using places.
;    This comes with several restrictions and complexity due to the restrictions on places.
;    Most crutially, it's a macro, the mapping function cannot have a closure,
;    and the call to parallel-map cannot be in the executed module.
;    It also has a somewhat complex signature to support startup/shutdown.
; 2) A concurrent thread pool.
;    While not parallel per se,
;    this can be used for parallelism if the mapping function uses, e.g., subprocesses.
;    As it uses simple threads, there are no restrictions on the mapping function.
;
; NB: the signatiures for the two functions are quite dissimilar.
; One is not a drop-in replacement for the other.

(provide
  current-parallel-worker-count
  parallel-map/place
  parallel-map/place/phony
  parallel-map/thread)

(require
  (for-syntax syntax/parse)
  racket/async-channel
  "serialize.rkt"
  "util.rkt")

(define current-parallel-worker-count (make-parameter 3))
(define current-parallel-progress-counter-period (make-parameter 50))

;;---------------------------------------------------------------------------------------------------
;; Place-based parallelism
;;---------------------------------------------------------------------------------------------------

(define-syntax-rule (make-worker-fun init-func work-func terminate-func)
  (λ ()
    (place ch
      (let ([initf init-func]
            [workf work-func]
            [termf terminate-func])
        (match-define (list self index init-data) (place-channel-get ch))

        (define config (initf index (deserialize init-data)))
        (place-channel-put ch self)
        (let loop ()
          (match (place-channel-get ch)
           [(cons 'kill ch)
            (termf index config)
            (place-channel-put ch 'dead)]
           [(cons self item)
            (with-handlers ([(λ (_) #t)
                             (λ (e)
                               (printf "\nwork function in place had exception ~v\n" e)
                               (exit))])
              (define res (cons self (serialize (workf config (deserialize item)))))
              ;(printf "res: ~a\n" res)
              (place-channel-put ch res))
            (loop)]))))))

(define (run-workers init-data make-worker generator-next? generator-next! #:eater [eater void] #:total [total #f])
  ; make all the workers and send them the init data
  (define workers (build-list (current-parallel-worker-count) (λ (_) (make-worker))))
  (displayln (format "Launching parallel computations with ~a workers" (length workers)))
  (define rv (box empty))
  (let ([d (serialize init-data)])
    (for ([i (length workers)] [wrkr workers]) (place-channel-put wrkr (list wrkr i d))))
  ; send every item in the list to an available worker
  (define counter (box 0))
  (define (handle-msg msg)
    (match msg
     ; if it's a pair, that's a work result
     [(cons w serialized-result)
      (define result (deserialize serialized-result))
      (set-box! rv (cons result (unbox rv)))
      ; also send results immediately to the eater
      ;(dprint "sending result to eater")
      (eater result)
      w]
      ; if it's only the worker, that's the init
     [w w]))
  (let loop ()
    (cond
     [(generator-next?)
      (define itm (generator-next!))
      (set-box! counter (add1 (unbox counter)))
      (when (= 0 (modulo (unbox counter) (current-parallel-progress-counter-period)))
        (dprint (format "Progress: ~a/~a" (unbox counter) (or total "?"))))
      (define wrkr (handle-msg (apply sync workers)))
      ;(printf "itm: ~a\n" itm)
      (place-channel-put wrkr (cons wrkr (serialize itm)))
      (loop)]
     [else (void)]))
  ; send a kill msg so we can sync one last time with every worker to get whatever they are finishing up
  (dprintf "done running, now sending termination events")
  (for ([w workers])
    (place-channel-put w (cons 'kill w))
    ;(dprintf "syncing")
    (handle-msg (place-channel-get w)))

  ;(dprintf "done running, now killing everything")
  (for-each place-kill workers)
  ; don't worry about ordering, just return in whatever order they came back in
  ; TODO use a vector to preserve ordering
  (unbox rv))

; parallel-map/place: ('a -> 'b), (('b, 'c) -> 'd), 'a, 'c list -> 'd list
;
; uses places to apply work-func to every item in lst.
; the callsite of this MUST NOT be in the main module!
; each worker runs init-func with init-data as the argument first,
; and the result of init-func is passed as the first argument to work-func.
;
; because it uses places, 'a, 'c, and 'd must satisy place-message-allowed?
; 'b, on the other hand, can be anything.
(define-syntax-rule (parallel-map/place-raw init-func work-func terminate-func init-data lst)
  (let ([make-worker (make-worker-fun init-func work-func terminate-func)])
    (define-values (next? next!) (sequence-generate lst))
    (run-workers init-data make-worker next? next! #:total (length lst))))

; TODO document
(define-syntax (parallel-map/place stx)
  (syntax-parse stx
   [(parallel-map/place
      (~or
        (~optional (~seq #:initialize initialize:expr)
                   #:name "#:initialize procedure")
        (~optional (~seq #:finalize finalize:expr)
                   #:name "#:finalize procedure")
        (~optional (~seq #:initial initial:expr)
                   #:name "#:initial object")
        (~once (~seq #:map work-func:expr)
               #:name "#:map procedure")
        (~once (~seq #:list lst:expr)
               #:name "#:list elements"))
      ...)
    (with-syntax ([init-func (if (attribute initialize) #'initialize #'(λ (a b) b))]
                  [term-func (if (attribute finalize) #'finalize #'void)]
                  [init-data (if (attribute initial) #'initial #'(void))])
       #'(parallel-map/place-raw init-func work-func term-func init-data lst))]))

; for testing prallel-map/place without the places to make stack traces better
(define (parallel-map/place/phony #:map f #:list lst #:initial [in (void)] #:initialize [finit (λ (a b) b)] #:finalize [fterm void])
  (define x (finit 0 in))
  (define res (map (curry f x) lst))
  (fterm x)
  res)

;;---------------------------------------------------------------------------------------------------
;; Thread-based pseudo-parallelism
;;---------------------------------------------------------------------------------------------------

(define (make-worker-thread f)
  (define chan (make-async-channel))
  (define t
    (thread
      (thunk
        ;(displayln "sending ready message")
        (async-channel-put chan 'ready)
        ; loop on received messages until we get a 'kill message
        (let loop ()
          (match (thread-receive)
           [`(work ,x)
            ;(displayln "got work!")
             ; TODO catch exceptions so this don't just deadlock on error
            (async-channel-put chan `(result ,(f x)))
            (loop)]
           ['kill
            ;(displayln "got kill message!")
            ; send something for the final sync in case we are not doing work.
            ; This may never be received, but the thread will still exit since the channel is async.
            (async-channel-put chan 'dead)
            (void)])))))
  (cons t chan))

(define (run-thread-pool f #:next? generator-next? #:next! generator-next! #:eater [eater void] #:total [total #f])
  ; make all the workers and send them this thread so they can send results back
  (define workers (build-list (current-parallel-worker-count) (λ (_) (make-worker-thread f))))
  (displayln (format "Launching concurrent computations with ~a thread workers" (length workers)))
  ; handle a message, adding any results in the message to the accumulator old-results
  (define (handle-result msg old-results)
    (match msg
     ['ready old-results]
     ['dead old-results]
     [`(result ,r)
      (eater r)
      (cons r old-results)]))
  ; send every item in the list to an available worker
  (define results
    (let loop ([results empty] [counter 1])
      (cond
       [(generator-next?)
        (define itm (generator-next!))

        (when (= 0 (modulo counter (current-parallel-progress-counter-period)))
          (dprint (format "Progress: ~a/~a" counter (or total "?"))))
        ;(displayln "awaiting message")
        (apply
          sync
          (map (λ (w)
                 (handle-evt (cdr w)
                             (λ (msg)
                               ;(printf "handling message ~a\n" msg)
                               (thread-send (car w) `(work ,itm))
                               (loop (handle-result msg results) (add1 counter)))))
               workers))]
       [else
        results])))
  ; send a kill msg so we can sync one last time with every worker to get whatever they are finishing up
  (dprintf "done running, now sending termination events")
  (for ([w workers]) (thread-send (car w) 'kill))
  (foldl handle-result results (map (compose async-channel-get cdr) workers)))

(define (parallel-map/thread f lst #:eater [eater void])
  (define-values (next? next!) (sequence-generate lst))
  (run-thread-pool f #:next? next? #:next! next! #:eater eater #:total (length lst)))

