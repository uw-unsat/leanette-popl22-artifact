#lang racket

(provide
  apply-rules-to-fixed-point
  apply-rules-to-fixed-point-of-set
  coverage-of-rule
  coverage-of-rules
  cluster-by-coverage
  coverage-of-individual-rules)

(require
  "../core/core.rkt"
  "../nonograms/debug.rkt"
  "../nonograms/dsl-pretty.rkt"
  "../nonograms/nonograms.rkt")

; Program?, environment? -> (or/c false? (listof integer?))
; returns the cells that are changed in this environment by this rule, or #f if 0 cells
; (that is, returns #f instead of empty).
; tctx: (or/c transition? false?) -- if transition?, then checks to ensure rule was valid. if false there is no check.
(define (cells-changed-by-rule prog env tctx)
  (define actions (interpret/deterministic prog env))
  (cond
   [(and tctx actions (ormap (λ (a) (not (action-compatible-with-transition? a tctx))) actions))
    (printf "INVALID RULE OHNOES\n~a\n~a\n" (pretty-format-transition tctx) (findf (λ (a) (not (action-compatible-with-transition? a tctx))) actions))
    (print prog)
    (displayln "\n")
    #f]
   [(and actions (not (empty? actions)))
    (define cells
      (append-map
        (λ (actn) (range (fill-action-start actn) (fill-action-end actn)))
        actions))
    (define start (line-cells (environment-line env)))
    (define lst
      (filter
        (λ (cidx)
          (cond
           [(or (< cidx 0) (>= cidx (length start)))
            (printf "RULE PRODUCED INVALID ACTION!\n~a\n~a\n~a\n" (debug-format-program prog) (pretty-format-line (environment-line env)) actions)
            (print prog)
            (displayln "\n")
            #f]
           [else (empty-cell? (list-ref start cidx))]))
        (remove-duplicates cells)))
    ;(and (not (empty? cells)) (remove-duplicates cells))]
    (and (not (empty? lst)) lst)]
   [else #f]))

(define (apply-changed-cells-to-line prog ctx changed-cells)
  (define val (Fill-val (Program-action prog)))
  (define actions (map (λ (idx) (fill-action val idx (add1 idx))) changed-cells))
  (foldl apply-action ctx actions))

(define (apply-changed-cells-to-transition-start prog tctx changed-cells)
  (define val (Fill-val (Program-action prog)))
  (define actions (map (λ (idx) (fill-action val idx (add1 idx))) changed-cells))
  (define new-start (foldl apply-action (line-transition-start tctx) actions))
  (struct-copy line-transition tctx [start new-start]))

(define (sum f lst)
  (apply + (map f lst)))

; (listof environment?), Program? -> ...
(define (changed-environments environments rule)
  (error "unimplemented"))

; Program?, (listof environment?) -> integer?
(define (coverage-of-rule all-environments rule)
  (sum
    (λ (env)
      (define actual-cells (cells-changed-by-rule rule env #f))
      (if actual-cells (length actual-cells) 0))
    all-environments))

(define (transition-has-work-remaining? tctx)
  (not (equal? (line-transition-start tctx) (line-transition-end tctx))))

(define (transition->environment trns) (create-environment (line-transition-start trns)))

(define (replace-transition-start tctx start)
  (struct-copy line-transition tctx [start start]))

(define (apply-rules-to-fixed-point all-rules start-transition)
  (define end-state
    (let loop ([to-test all-rules] [env (transition->environment start-transition)])
      (cond
       [(empty? to-test)
        (environment-line env)]
       [else
        (define next (car to-test))
        (define changed (cells-changed-by-rule next env (replace-transition-start start-transition (environment-line env))))
        (cond
         [changed
          (define new-trns (struct-copy line-transition start-transition [start (apply-changed-cells-to-line next (environment-line env) changed)]))
          (cond
           [(transition-has-work-remaining? new-trns)
            (loop (cdr to-test) (transition->environment new-trns))]
           [else (line-transition-start new-trns)])]
         [else (loop (cdr to-test) env)])])))
  (if (equal? end-state (line-transition-start start-transition))
      end-state
      (apply-rules-to-fixed-point all-rules (struct-copy line-transition start-transition [start end-state]))))

(define (apply-rules-to-fixed-point-of-set transitions rules)
  (define modified
    (filter-map
      (λ (t)
        (define end-state (apply-rules-to-fixed-point rules t))
        (and (not (equal? end-state (line-transition-start t)))
             (cons
               (line-transition-size (struct-copy line-transition t [end-cells (line-cells end-state)]))
               (struct-copy line-transition t [start end-state]))))
      transitions))
  (values
    (apply + (map car modified))
    (map cdr modified)))

(define (coverage-of-rules starting-transitions rules)
  (unless (list? starting-transitions) (error "transitons must be a list"))
  (unless (list? rules) (error "rules must be a list"))
  (let loop ([transitions starting-transitions] [acc 0])
    (cond
     [(empty? transitions)
      acc]
     [else
      ; apply all rules to fixed point, getting the total filled cells and the modified lines
      (define-values (total-changed new-transitions) (apply-rules-to-fixed-point-of-set transitions rules))
      ; break these new transitions into subspaces
      (define subspaces
        (for*/list ([tctx new-transitions]
                    ; throw out any lines that are complete to not waste time
                    #:when (transition-has-work-remaining? tctx)
                    ;#:when #f
                    [sm (find-subspace-mappings (line-transition-start tctx))])
          (apply-subspace-mapping-t sm tctx)))
      ; repeat on this new set of lines, accumulating the total score
      (loop subspaces (+ total-changed acc))])))

(define (cluster-init _ transitions)
  (map transition->environment transitions))

(define (cluster-work envs rule)
  (cons
    rule
    (remove-duplicates
      (append-map
        (λ (env)
          (define actions (interpret/deterministic rule env))
          (cond
           [actions
            (define cells
              (remove-duplicates
                (append-map
                  (λ (actn) (range (fill-action-start actn) (fill-action-end actn)))
                  actions)))
             (map (curry cons (environment-line env)) cells)]
            ;(map (curry cons (environment-line env)) actions)]
           [else empty]))
        envs))))

; (listof line-transition?), (listof Program?) -> (listof (listof Program?))
; Cluster the given rules by their coverage on the test set.
; Rules are grouped together if they engender precisely the same set of actions on the test set.
; This uses simple (non-fixed point) coverage since it's reasonable to care only how they behave in a first-order manner.
(define (cluster-by-coverage transitions rules #:filter-subclusters? [filter-subclusters? #f])
  (define coverage-elements (parallel-map/place #:initial transitions #:initialize cluster-init #:map cluster-work #:list rules))
  (define clusters (group-by (compose list->set cdr) coverage-elements))
  (printf "there are ~a clusters from ~a rules\n" (length clusters) (length rules))
  ; remove any clusters that are strict subsets of other clusters
  (when filter-subclusters?
    (define cluster-sets (map (λ (c) (list->set (cdr (first c)))) clusters))
    (set! clusters
      (filter-map
        (λ (c s)
          (define drop? (ormap (curry proper-subset? s) cluster-sets))
          (and (not drop?) c))
        clusters
        cluster-sets))
    (printf "down to ~a clusters after removing subclusters\n" (length clusters)))
  ; drop the coverage stuff and leave only the rules
  (map (λ (c) (map car c)) clusters))

(define (par-work-rule-coverage tctxs rule)
  (cons rule (coverage-of-rules tctxs (list rule))))

; (listof line-transition?), (listof Program?) -> (listof (pairof Program? integer?))
(define (coverage-of-individual-rules transitions rules)
  (parallel-map/place #:map par-work-rule-coverage #:initial transitions #:list rules))

