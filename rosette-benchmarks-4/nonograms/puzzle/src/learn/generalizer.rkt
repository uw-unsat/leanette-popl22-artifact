#lang racket

(provide
  synthesize-general-rules-at-level)

(require
  (only-in rosette clear-asserts!)
  data/queue
  racket/async-channel
  "../core/core.rkt"
  "../nonograms/nonograms.rkt"
  "learn.rkt"
  "synthesize.rkt")

;ALGROTIHM:
;
;for a given fixed set of transitions with expressible actions (call them deltas because we know the action), D:
;
;let R = ∅
;
;for counter i = 1..til we're bored, probably 2:
;  for all t ∈ D:
;    for all b ∈ set of subsets of bindings(t) with size i:
;      if ∃ r∈R s.t b = bindings(r) ∧ r(start(t)) = end(t):
;        continue
;      else:
;        let r = try synthesize maximal rule for t with bindings b
;        if r: R <- R ∪ {r}
;  also add all the reachable states of D with R to D', and work on that until empty? I guess this is a queue

; bindings are "the same" if they are set equivalent, ignoring NoPattern.
; since we happen to always enumerate them in the same order, we can use list equality instead of set equality,
; as long as we remove all the NoPatterns. So that's all we have to do.
; Obviously, the relies on lowest-bindings-of-line to actually enumerate bindings in a consistent order.
; (listof Binding?) -> key?
(define (binding->key bnd) (filter ListBinding? bnd))

(define (ruleset-rules-of-binding ruleset bnd)
  (hash-ref ruleset (binding->key bnd) empty))

(define (ruleset->list ruleset)
  (apply append (hash-values ruleset)))

(define (ruleset-add! ruleset x)
  (define key (binding->key (Program-pattern x)))
  (define lst (hash-ref ruleset key empty))
  (hash-set! ruleset key (cons x lst)))

(define (reachable-states-from-rule dctx prog)
  empty)
  ;(error "unimplemented"))

(define (rule-covers? dctx prog)
  (define env (create-environment (line/fill-line dctx)))
  (define actions (interpret/deterministic prog env))
  (member (line/fill-action dctx) actions))

; TODO throw out items that are already covered
; chooses a next work item from the list such that no active work items have the same key
(define (work-item-status ruleset active-list item)
  (define bnd (cdr item))
  (cond
   ; if it's covered by a rule we've already found, the drop it entirely
   [(ormap (curry rule-covers? (car item)) (ruleset-rules-of-binding ruleset bnd)) 'drop]
   ; if we're currently working on a rule with the same binding, then postpone (since we'll possibly drop it later)
   [(ormap (λ (pr) (equal? (cdr pr) bnd)) active-list) 'postpone]
   [else 'continue]))

(define (subsets-of-size sz lst)
  (define len (length lst))
  (cond
   [(<= sz 0) (list empty)]
   [(> sz len) empty]
   [(equal? sz len) (list lst)]
   [else
    (match-define (cons head tail) lst)
    (append
      (map (curry cons head) (subsets-of-size (sub1 sz) tail))
      (subsets-of-size sz tail))]))

(define (all-subset-bindings-of-size dctx size)
  (define full (lowest-bindings-of-line (line/fill-line dctx)))
  (dprintf "full: ~v" full)
  (define sub-indices (subsets-of-size size (range (length full))))
  (dprintf "subs: ~v" sub-indices)
  (map
    (λ (idxs)
      (mapi (λ (i x) (if (member i idxs) x (NoPattern))) full))
    sub-indices))

(define (serialize-work-item item)
  (cons (serialize-line/fill (car item)) (serialize-program (cdr item))))

(define (deserialize-work-item item)
  (cons (deserialize-line/fill (car item)) (deserialize-program (cdr item))))

(define (init-func i d)
  (debug-print? #t)
  d)

(define (work-func cfg work-item)
  (match-define (learn-config _ ce-params fp-params prog-params fi-params) cfg)
  (match-define (cons dctx bnd) (deserialize-work-item work-item))
  (dprintf "generating rules for delta ~v, binding ~v" dctx bnd)
  (define res
    (synthesize-generalization
      #:delta dctx
      #:binding bnd
      #:counter-example-parameters ce-params
      #:force-positive-parameters fp-params
      #:force-improvement-parameters fi-params
      #:program-sketch-parameters prog-params))
  (dprintf "got result")
  (cons work-item (serialize-generalization-results res)))

(define (synthesize-general-rules-at-level
          starting-deltas
          binding-size
          #:counter-example-parameters ce-params
          #:force-positive-parameters fp-params
          #:force-improvement-parameters fi-params
          #:program-sketch-parameters prog-params)
  (define ruleset (make-hash))
  (define results empty)
  (define cfg (learn-config #f ce-params fp-params prog-params fi-params))

  (define work-queue (make-queue))

  (define (eat-result item)
    (match-define (cons input result) item)
    ; TODO update the result table
    (set! results (cons (cons (car input) result) results))
    (for ([pr (cdr result)])
      (ruleset-add! ruleset (deserialize-program (cdr pr))))
    ; TODO add all reachable states (that we haven't already visited) to the work list
    (void))

  (for-each (curry enqueue! work-queue) starting-deltas)

  (let loop ()
    (cond
     [(queue-empty? work-queue)
      (void)]
     [else
      (define dctx (dequeue! work-queue))
      (for ([bnd (all-subset-bindings-of-size dctx binding-size)])
        (define item (cons dctx bnd))
        (match (work-item-status ruleset empty item)
         ['drop
          (dprintf "skipping ~v because already covered" item)
          (void)]
         ['continue
          (eat-result (work-func cfg (serialize-work-item item)))]))
      (loop)]))

  results)

