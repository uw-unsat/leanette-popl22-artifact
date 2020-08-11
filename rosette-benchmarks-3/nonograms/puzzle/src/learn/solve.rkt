#lang racket

(provide
  find-maximal-transition-with-rules
  build-transition-solution-graph
  board-solvable-with-rules?
  rollout-board-solution
  run-board-solution-rollouts)

(require
  "../core/core.rkt"
  "../nonograms/debug.rkt"
  "../nonograms/nonograms.rkt")

; two environments! one flipped so we can apply rules in reverse
(struct environment-group (forwards backwards))
(define (environment-group-line envgrp)
  (environment-line (environment-group-forwards envgrp)))

(define (create-environment-group ctx)
  (environment-group
    (create-environment ctx)
    (create-environment (flip-line ctx))))

(define (possible-actions-of-rule-single-env env prog)
  (or (interpret/deterministic prog env) empty))

; environment-group?, Program? -> (listof fill-action?)
(define (possible-actions-of-rule envgrp prog)
  (append
    (possible-actions-of-rule-single-env (environment-group-forwards envgrp) prog)
    (map (curry flip-action (line-length (environment-group-line envgrp))) (possible-actions-of-rule-single-env (environment-group-backwards envgrp) prog))))

; (listof Program?), environment-group?, (boxof boolean?) -> line?
; apply all possible rules to line-info, returning the new line-info.
; if anything changed, the box are-actions? is set to true (otherwise left alone)
(define (maximally-solve all-rules envgrp #:are-actions? are-actions? #:used-rules [used-rules #f])
  (define (test-rule r state)
    ; always apply rules to the original context, but apply actions to the ongoing context
    (foldl
      (λ (a s)
        (define s2 (apply-action a s))
        (unless (equal? s s2)
          (set-box! are-actions? #t)
          (when used-rules (set-add! used-rules r)))
        s2)
      state
      (possible-actions-of-rule envgrp r)))

  (foldl test-rule (environment-group-line envgrp) all-rules))

; (listof Program?), (pairof environment? board-line?), (boxof boolean?) -> board-line?
; apply all possible rules to line-info, returning the new line-info.
; if anything changed, the box are-actions? is set to true (otherwise left alone)
(define (maximally-solve* all-rules are-actions? line-info)
  (match-define (cons env bl) line-info)
  ; HACK this ruins the cost savings of passing in environment?, need to finish refactoring later
  (define envgrp (create-environment-group (environment-line env)))
  (struct-copy board-line bl [line (maximally-solve all-rules envgrp #:are-actions? are-actions?)]))

; (listof rule?), line? -> line-transition?
(define (find-maximal-transition-with-rules all-rules start-state #:used-rules-box [used-rules-box (box #f)] #:intermediate-states-box [intermediate-states-box (box #f)])
  (define used-rules (mutable-seteq))
  (set-box! intermediate-states-box empty)
  (define end-state
    (let loop ([ctx start-state])
      (set-box! intermediate-states-box (cons ctx (unbox intermediate-states-box)))
      (define progress? (box #f))
      ; first, apply every rule to the base context.
      (define ctx* (maximally-solve all-rules (create-environment-group ctx) #:are-actions? progress? #:used-rules used-rules))
      ; stop at fixed point
      (cond
       [(unbox progress?)
        ; then find (using the oracle) all potential subcontexts.
        (define sms (find-subspace-mappings ctx*))
        ; apply all possible rules to this subcontext until fixed point
        (define subs (map (λ (sm) (loop (apply-subspace-mapping sm ctx*))) sms))
        (define final
          (foldl
            (λ (sm sub acc)
              (reverse-subspace-mapping sm acc sub))
            ctx* sms subs))
        (loop final)]
       [else ctx])))
  ;(printf "number of used actions: ~a\n" (set-count used-rules))
  (set-box! used-rules-box (set->list used-rules))
  (line-transition start-state (line-cells end-state)))

; (listof Program?), line-transition? -> digraph?
; builds a graph of all possible solutions for this transition, with edges labeled with the rules needed for those transitions
(define (build-transition-solution-graph rules main-tctx)
  (define grph (make-digraph identity))
  ;(printf "rules? ~a\ntctx: ~a\n" (andmap Program? rules) main-tctx)

  ; a dummy sink node that can never be satisfied.
  ; this is used because the cover algorithm uses sinks as implicit goals, and having a dummy sink is an easy way to force
  ; non-goal nodes to be intermediate nodes.
  (define bad-sink (dg-add-node! grph 'unreachable))
  (define (add-internal-node! val)
    (define n (dg-add-node! grph val))
    (dg-add-edge! n bad-sink empty)
    n)

  ;(printf "new loop: ~a\n" main-tctx)

  (let loop ([tctx main-tctx] [starting-node (add-internal-node! 'source)] [prev-mapping (identity-subspace-mapping (line-transition-start main-tctx))])
    ; get every destination state for every program, broken into individual cells
    (define start-state (line-transition-start tctx))
    (define envgrp (create-environment-group start-state))
    (define env (environment-group-forwards envgrp))
    (define components
      (remove-duplicates
        (for/list ([idx (length rules)]
                   [p rules]
                   #:when #t
                   [a (possible-actions-of-rule envgrp p)]
                   #:when #t
                   [offset (in-range (- (fill-action-end a) (fill-action-start a)))])
          (define start (+ offset (fill-action-start a)))
          (cons idx (fill-action (fill-action-value a) start (add1 start))))))
    ; partition by these cell actions, but discard anything that is ineffective
    (define classes
      (filter
        (λ (cls)
          (define key (cdar cls))
          (action-compatible-with-and-impactful-for-transition? key tctx))
        (partition-by-key cdr components)))
    ; create a mapping from action as (cons val start) to program indices
    (define mapping (make-hash (for/list ([cls classes]) (cons (cdar cls) (map car cls)))))

    (define end-state (foldl apply-action (environment-line env) (hash-keys mapping)))
    (define expected-end (line-transition-end tctx))

    ;(printf "checking:\n\t~a ->\n\t~a\n" (pretty-format-line start-state) (pretty-format-line end-state))

    (cond
     [(equal? end-state expected-end)
      ;(printf "reached end!\n" )
      (void)]
     [else
      ;(printf "more to go: ~a -> ~a\n" end-state expected-end)
      (unless (line-weaker? end-state expected-end)
        (printf "bad transition: ~a -> ~a\n" end-state expected-end)
        (error "something wrong! applied an invalid rule!"))
      (define sms (find-subspace-mappings end-state))
      ; don't generate the chain unless we're going to use it
      (unless (empty? sms)
        ;(printf "subspaces: ~a\n" sms)
        ; create a chain (to form a conjuction) as a prereq for these subproblems
        (define end-node
          (let rec ([prev starting-node] [remaining (hash->list mapping)])
            (match remaining
             ['() prev]
             [(cons (cons key val) tail)
              (define next (add-internal-node! `(chain ,tctx ,key)))
              (dg-add-edge! prev next val)
              (rec next tail)])))
        (for ([sm sms])
          ; TODO need some kind of function to reverse the mapping for node names
          (define sub-tctx (apply-subspace-mapping-t sm (struct-copy line-transition tctx [start end-state])))
          (define full-mapping (compose-subspace-mappings prev-mapping sm))
          (loop sub-tctx end-node full-mapping))
        (void))])

    ; make a node for each transition arrived at, with an edge containing the required rules
    (for ([(key val) (in-hash mapping)])
      ; name of the node should be whatever it would be in the root space, so reverse transform the action by the full mapping
      (define n (dg-add-node! grph (reverse-subspace-mapping-a prev-mapping key)))
      (dg-add-edge! starting-node n val))
    (void))

  ;(printf "grph order: ~a, size: ~a, avg edge len: ~a, tctx: ~a\n" (dg-order grph) (dg-size grph) (/ (apply + (map length (dg-edge-values grph))) (dg-size grph)) main-tctx)
  grph)

(define (board-solvable-with-rules? rule-set brd)
  (define (try-solve typ changed?)
    (define bls (board-lines-of-type typ brd))
    (define envbls (map (λ (bl) (cons (create-environment (board-line-line bl)) bl)) bls))
    (define new-bls (map (curry maximally-solve* rule-set changed?) envbls))
    (for-each (curry board-set-line! brd) new-bls))

  ; alternate between applying all rules to rows and all rules to columns
  (let loop ()
    (define changed? (box #f))
    (try-solve 'row changed?)
    (try-solve 'col changed?)
    (cond
     ; if solved, we're done
     [(board-solved? brd) #t]
     ; if nothing changed, we're stuck
     [(not (unbox changed?)) #f]
     ; otherwise keep going
     [else (loop)])))

; using oracle, solves this board one line at a time, choosing actions randomly.
; returns a list (perhaps with duplicates) of transitions used during the solution process.
; SOME IMPLEMENTATION NOTES
; - looks at all rows, finds their maximal transitions (if they exist).
; - chooses one transition uniformly randomly, and applies the entire thing
(define (rollout-board-solution orig-brd)
  (define brd (copy-board orig-brd))
  (define (transition-for bl)
    (define tctx (strongest-deduction-of (board-line-line bl)))
    (and tctx (not (equal? (line-transition-start tctx) (line-transition-end tctx))) (cons bl tctx)))

  (let loop ([acc empty])
    (cond
     [(board-solved? brd) (reverse acc)]
     [else
      (define all-infos (board-line-infos brd))
      (define all-tctxs (filter-map transition-for all-infos))
      (cond
       [(empty? all-tctxs) #f]
       [else
        ; choose a transition randomly, apply it, and loop until board is solved
        (match-define (cons bl tctx) (choose-random all-tctxs))
        (board-set-line! brd (struct-copy board-line bl [line (line-transition-end tctx)]))
        (loop (cons tctx acc))])])))

(define (run-board-solution-rollouts boards rollouts-per-board)
  (define items (append-map (λ (b) (make-list rollouts-per-board b)) boards))
  (define r
    (parallel-map/place
      #:map (λ (_ item) (rollout-board-solution item))
      #:list items))
  (printf "len: ~a\nitems: ~a\n" (length r) (map length r))
  (apply append r))

