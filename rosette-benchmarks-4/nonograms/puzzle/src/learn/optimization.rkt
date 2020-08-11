#lang racket

(provide
  make-optimization-parameters
  (struct-out optimization-item)
  full-coverage-score
  choose-optimal-set
  run-ruleset-optimization
  run-multiple-ruleset-optimzations)

(require
  rosette/solver/smt/z3
  "solve.rkt"
  "cover.rkt"
  "analysis.rkt"
  "coverage.rkt"
  "../core/core.rkt"
  "../nonograms/dsl-pretty.rkt"
  "../nonograms/nonograms.rkt")

(standard-struct optimization-parameters (rules transitions max-count))
(define (make-optimization-parameters
          #:rules r
          #:transitions t
          #:max-count c)
  (optimization-parameters r t c))

(standard-struct optimization-item (program score))

(define (coverage-score rules grph)
  (define goals (dg-sinks grph))
  (define start
    (let ([sources (dg-sources grph)])
      (unless (= 1 (length sources)) (error "graphs may only have one source!"))
      (first sources)))

  (define (edge-usable? e)
    (and
      (not (empty? e))
      (ormap (curry set-member? rules) e)))

  ; NOTE if we switch to andmap, have to filter items with only the unreachable edge
  (sum
    (λ (nde)
      ; HACK
      ;(or (equal? (dg-node-value nde) 'unreachable)
      (if (dg-reachable? start nde #:filter-edge edge-usable?) 1 0))
    goals))

(define (sum f lst)
  (apply + (map f lst)))

(define (full-coverage-score graphs)
  (define (f g)
    ; subtract off the unreachable sink
    (sub1 (length (dg-sinks g))))
  (sum f graphs))

(define (choose-optimal-set graphs #:max-result-size [max-result-size 10])
  (define all-edges (append-map dg-edge-values graphs))
  (define max-element (apply max (apply append all-edges)))
  (define all-rules (range (add1 max-element)))
  (define original (list->seteq all-rules))
  ;(define prev-data (map (λ (_) (cons #f #f)) test-set))

  (define (covered-count rules)
    ;(dprint (set->list rules))
    ;(printf "checking count for set with ~a\n" (debug-format-program (car rules)))
    (sum (λ (g) (coverage-score rules g)) graphs))

  (dprintf "possible coverage: ~a" (covered-count original))

  ; try adding one at a time
  (let loop ([current-set (seteq)])
    (printf "in loop, round ~a: # covered: ~a\n" (set-count current-set) (covered-count current-set))
    (cond
     [(>= (set-count current-set) max-result-size)
      (sort (set->list current-set) <)]
     [else
      (define potential (set->list (set-subtract original current-set)))
      (define current-list (set->list current-set))
      (define to-add (argmax (λ (r) (covered-count (set-add current-set r))) potential))
      (loop (set-add current-set to-add))])))

(define (parinit _ data)
  data)

;(define (par-init-rule-coverage _ transitions)
;  (map (compose create-environment line-transition-start) transitions))

(define (par-work-rule-coverage tctxs rule)
  (cons rule (coverage-of-rules tctxs (list rule))))

; (listof (pairof Program? real?)) -> (pairof Program? real?)
(define (best-cheapest-rule scores)
  (define best-score (apply max (map cdr scores)))
  (define contenders (filter (λ (pr) (= (cdr pr) best-score)) scores))
  (argmin (λ (pr) (program-cost (car pr))) contenders))

; for testing only, typically we run just one, but for testing it's really wasteful to make the graphs twice
(define (run-multiple-ruleset-optimzations params config-list #:graph-box [graph-box (box #f)])
  (define rules (optimization-parameters-rules params))
  (define transitions (optimization-parameters-transitions params))
  (printf "building graphs.\n")
  (define graphs (parallel-map/place #:initialize parinit #:map build-transition-solution-graph #:initial rules #:list transitions))
  ;(printf "done building graphs.\n")
  ;(define graphs (map (curry build-transition-solution-graph rules) transitions))
  (define rule-count (optimization-parameters-max-count params))
  (set-box! graph-box graphs)
  (for/list ([config config-list])
    (time
      (match config
       ['greedy (choose-optimal-set graphs #:max-result-size rule-count)]
       ['optimal (find-minimum-weak-cover-for-graph graphs rule-count)]))))

(define (par-get-score transitions rules)
  (cons (first rules) (coverage-of-rules transitions rules)))

; optimization-parameters? -> (listof optimization-item?)
(define (run-simple-optimization params)
  (define all-rules (optimization-parameters-rules params))
  (define transitions (optimization-parameters-transitions params))
  ; do the simple obvious thing: find the best rule according to fixed-point coverage score, then try adding more until limit is hit
  (let loop ([remaining all-rules] [accumulated empty])
    (cond
     [(or (empty? remaining) (>= (length accumulated) (optimization-parameters-max-count params)))
      ; order by best rule first
      (reverse accumulated)]
     [else
      (define acc-rules (map optimization-item-program accumulated))
      (define old-score (coverage-of-rules transitions acc-rules))
      (printf "in loop round ~a: # covered: ~a\n" (length accumulated) old-score)
      (define scores (parallel-map/place #:map par-get-score #:initial transitions #:list (map (λ (r) (cons r acc-rules)) remaining)))
      (define chosen (best-cheapest-rule scores))
      ; remaining consists of any not-chosen rule that still made progress
      (define new-remaining
        (filter-map
          (λ (pr) (and (> (cdr pr) old-score) (car pr)))
          (remq chosen scores)))
      (printf "dropped ~a rules for being ineffective\n" (- (sub1 (length remaining)) (length new-remaining)))
      (define item (optimization-item (car chosen) (cdr chosen)))
      (loop new-remaining (cons item accumulated))])))

(define use-new-optimization? #t)

; optimization-parameters? -> (listof Program?)
(define (run-ruleset-optimization params)
  ;(cond
   ;[use-new-optimization?
   ; (run-simple-optimization params)
   ;[else
   ; (define indices (first (run-multiple-ruleset-optimzations params (list 'greedy))))
   ; (map (curry list-ref (optimization-parameters-rules params)) indices)]))
  (run-simple-optimization params))

