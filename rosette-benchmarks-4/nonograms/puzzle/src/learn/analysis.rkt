#lang rosette

(provide
  load-training-results
  load-training-results*
  training-results->programs
  coverage-for-delta
  count-coverage-of-programs
  count-coverage-of-programs*
  determine-rule-coverage
  find-minimal-covering-core
  determine-minimal-coverage-cores
  find-closest-rule-to
  filter-unsound-rules)

(require
  rosette/solver/smt/z3
  "solve.rkt"
  "cegis.rkt"
  "learning.rkt"
  "../core/core.rkt"
  "../nonograms/dsl-pretty.rkt"
  "../nonograms/nonograms.rkt")

(define (load-training-results path)
  (define-values (parent-dir file-name _) (split-path path))
  (printf "parent dir: ~a\n" parent-dir)
  (printf "file name: ~a\n" file-name)

  (define all-paths
    (filter
      (λ (fn)
        (string-prefix? (path->string fn) (path->string path)))
      (directory-list parent-dir #:build? #t)))

  (printf "loading results from paths:\n\t~a\n" all-paths)

  (define result-groups (append-map deserialize-from-file all-paths))
  ; the training results
  ; flip all the rules so the most general come first
  (define work-results (flatten-once (map reverse result-groups)))
  work-results)

; like load-training-results, but, instead of flattening the list, returns a list of the filenames paired with the results for that file
(define (load-training-results* path)
  (define-values (parent-dir file-name _) (split-path path))
  (printf "parent dir: ~a\n" parent-dir)
  (printf "file name: ~a\n" file-name)

  (define all-paths
    (filter
      (λ (fn)
        (string-prefix? (path->string fn) (path->string path)))
      (directory-list parent-dir #:build? #t)))

  (printf "loading results from paths:\n\t~a\n" all-paths)

  (for/list ([p all-paths])
    (define results (flatten-once (map reverse (deserialize-from-file p))))
    (define-values (d name e) (split-path p))
    (cons name results)))

(define (training-results->programs training-results)
  (define-values (success-results not-successes) (partition work-result-success? training-results))
  (define successes (map work-result->ruledata success-results))
  ; for some reason, removing duplicates here takes an enternity.
  ; if the the caller does it in a main file it's very fast.
  (map ruledata-program successes))

; (and/c Program? concrete?), (and/c line/fill? concrete?) -> (and/c boolean? concrete?)
; true iff evaluating the given program with the given line context results in the given fill action.
; use only when both program and context/action are concrete.
(define (program-matches-fill?/all-concrete program dctx [env #f])
  (match-define (line/fill ctx action) dctx)
  ;(dprintf "action: ~a" action)
  ;(dprintf "result ~a" (interpret/deterministic program (or env (create-environment ctx))))
  (define soln
    (solve
      (assert
        (member
          action
          (interpret/deterministic program (or env (create-environment ctx)))))))
  (sat? soln))

(define (count-work dctxs item)
  (define prog (cdr item))
  (define (works-on-any? dctx-list)
    (ormap (curry program-matches-fill?/all-concrete prog) dctx-list))
  (define result (map works-on-any? dctxs))
  (cons (car item) result))

(define (check-partial-condition-program program env expected)
  (define (check binding)
    ; figure out if this program is a subset of the expected action or incompatible with it
    (define actn (interpret/nondeterministic program env #:binding-assignments binding))
    (and actn
      (hasheq
        'binding binding
        'subset? (action-weaker? actn expected)
        'action (fill-action->string actn))))

  (when (empty?  (filter-map check (all-bindings-for-pattern program env)))
    (printf "~a\n" (pretty-print-program program))
    (printf "~a\n" (all-bindings-for-pattern program env))
    (flush-output (current-output-port))
    (error (format "something wierd! ~v ~v ~a" (environment-line env) expected (condition-applies?/deterministic program env))))

  (hasheq
    'program program
    'examples (filter-map check (all-bindings-for-pattern program env))))

; (vectorof Program?), line/fill? -> any
(define (coverage-for-delta progs dctx)
  ; find the best program(s) for this item. Find all programs that (in order of preference)
  ; - the program covers
  ; - the binding/condition or binding/action cover
  ; - the binding covers, action correct parity
  (define (getprog i) (vector-ref progs i))

  ; first filter to all programs with matching bindings.
  (define env (create-environment (line/fill-line dctx)))
  (define actn (line/fill-action dctx))
  (define tctx (line/fill->transition dctx))
  (define fill-type (fill-action-value (line/fill-action dctx)))
  (define potential
    (filter
      (λ (i)
        (and (binding-applies? (getprog i) env)
             (equal? (Fill-val (Program-action (getprog i))) fill-type)))
      (range (vector-length progs))))
  ; grab the ones that the program matches
  (define-values (covered uncovered) (partition (λ (i) (program-matches-fill?/all-concrete (getprog i) dctx env)) potential))
  ; for the rest, for any interpretation of the bindings, figure out if either the condition or action is covered.
  (define-values (covered/condition uncovered*) (partition (λ (i) (condition-applies?/deterministic (getprog i) env)) uncovered))
  (define-values (covered/action uncovered**)
    (partition
      (λ (i)
        (define actns (interpret/deterministic/nocondition (getprog i) env))
        (and actns (member actn actns)))
      uncovered*))
  ; binding matches and action has correct parity, but nothing else
  (hasheq
    'covered (map getprog covered)
    'condition (map (λ (i) (check-partial-condition-program (getprog i) env actn)) covered/condition)
    'action (map getprog covered/action)
    'binding (map getprog potential)))

; have to combine the results from each
;(define (merge-results r1 r2)
;  (define (merge key) (set-union (hash-ref r1 key) (hash-ref r2 key)))
;  (let* ([covered (merge 'covered)]
;         [condition (merge 'condition)]
;         [action (merge 'action)]
;         [uncovered (merge 'uncovered)]
;         [s2 (set-union covered condition action)])
;    (hasheq
;      'covered covered
;      'condition (set-subtract conditoin covered)
;      'action (set-subtract conditoin covered)
;      'uncovered (set-subtract uncovered s2))))

(define (count-work* progs deltas)
  (define results (map (curry coverage-for-delta progs) deltas))
  (cons deltas results))

; (listof Program?), (listof (listof line/fill?)) -> (vectorof (listof boolean?))
(define (count-coverage-of-programs
          #:all-programs programs
          #:all-deltas deltas)
  (define worklist (mapi (λ (i p) (cons i p)) programs))
  (define results (parallel-map/place #:map count-work #:initial deltas #:list worklist))
  (define v (make-vector (length programs) #f))
  (for ([pr results])
    (match-define (cons i c) pr)
    (vector-set! v i c))
  v)

; (listof Program?), (listof (listof line/fill?)) -> (listof hash-eq?)
; new, more advanced version that shows which programs cover which deltas, with grades of coverage
(define (count-coverage-of-programs*
          #:all-programs programs
          #:all-deltas deltas)
  (define progvec (list->vector programs))
  (parallel-map/place #:map count-work* #:initial progvec #:list deltas))


(define (parinit-for-solver index data)
  (current-solver (z3))
  data)

(define (parterm-for-solver index data)
  (solver-shutdown (current-solver)))

(define (find-maximal-transition-with-rules-pr rules ctx)
  (define used (box #f))
  (define tctx (find-maximal-transition-with-rules rules ctx #:used-rules-box used))
  (cons (unbox used) tctx))

; (listof Program?), (listof line/fill?) -> (listof (or/c false? (listof Program?)))
; for each delta, calculates whether it is covered by the given rules and returns a
; list (one entry per delta) of:
; - false if not covered
; - a list of sufficient (but perhaps not necessary) rules for coverage.
(define (determine-rule-coverage all-rules all-deltas)
  ; first combine deltas into start cells
  (define contexts (remove-duplicates (map line/fill-line all-deltas)))
  ; find the maximal transition (with rules) for each transition
  (define used-rule-transition-pairs
    (parallel-map/place
      #:initialize parinit-for-solver
      #:map find-maximal-transition-with-rules-pr
      #:finalize parterm-for-solver
      #:initial all-rules
      #:list contexts))
  (define transitions (map cdr used-rule-transition-pairs))
  (define line->pair (make-hash (map (λ (t) (cons (line-transition-start (cdr t)) t)) used-rule-transition-pairs)))
  ; then, for each transition, figure out which of the deltas it covered
  (define covered?
    (map
      (λ (d)
        (match-define (cons used tctx) (hash-ref line->pair (line/fill-line d)))
        (and (action-compatible-with-transition? (line/fill-action d) tctx)
             used))
      all-deltas))
  covered?)

; (listof Program?), line/fill? -> (listof Program?)
; Greedily finds a minimal core of the given rules that covers the given delta.
; Intention is to tuse the sufficient sets returned through determine-rule-coverage rather than the entire set.
(define (find-minimal-covering-core rules delta)
  (match-define (line/fill start action) delta)
  (define (covered? subset)
    (define tctx (find-maximal-transition-with-rules subset start))
    (action-compatible-with-transition? action tctx))
  (let loop ([kept empty] [remaining rules])
    (match remaining
     [(cons head tail)
      ; attempt to drop the next rule, in either case keep going with the remainder
      (define to-keep
        (if (covered? (append kept tail)) kept (cons head kept)))
      (loop to-keep tail)]
     [else
      ; flip it so they are in the original order they were given
      (reverse kept)])))

(define (dmcc-work _ item)
  (match-define (list idx rules delta) item)
  (and rules
       (cons idx (find-minimal-covering-core rules delta))))

(define (determine-minimal-coverage-cores coverage-list delta-list)
  (define len (length coverage-list))
  (define pairs (map list (range len) coverage-list delta-list))
  (define vec (make-vector len #f))
  (define results
    (parallel-map/place
      #:initialize parinit-for-solver
      #:map dmcc-work
      #:finalize parterm-for-solver
      #:list pairs))
  (for ([r results])
    (when r
      (vector-set! vec (car r) (list->set (cdr r)))))
  vec)

(define (cells-filled-by-rule prog env)
  (define actions (interpret/deterministic prog env))
  (cond
   [(and actions (not (empty? actions)))
    (define cells
      (append-map
        (λ (actn) (range (fill-action-start actn) (fill-action-end actn)))
        actions))
    (remove-duplicates cells)]
   [else #f]))

(define (sum f lst)
  (apply + (map f lst)))

; (listof transition?), Program?, (listof Program?) -> Program?
; finds the best matching rule for the given program.
; Prefers supersets, but if doesn't exist, prefers biggest subset.
; On tie, prefers simplest.
(define (find-closest-rule-to test-set test-rule other-rules)
  ; first calculate all starting state/action-list pairs for the test rule
  (define items
    (filter-map
      (λ (tctx)
        (define env (create-environment (line-transition-start tctx)))
        (define cells (cells-filled-by-rule test-rule env))
        (and cells (cons env cells)))
      test-set))
  (define all-environments (map (compose create-environment line-transition-start) test-set))
  (define (item-score r)
    (sum
      (λ (pr)
        (match-define (cons env target-cells) pr)
        (define actual-cells (cells-filled-by-rule r env))
        (if actual-cells
            (- (length target-cells) (length (set-subtract target-cells actual-cells)))
            0))
      items))
  (define (total-score r)
    (sum
      (λ (env)
        (define actual-cells (cells-filled-by-rule r env))
        (if actual-cells (length actual-cells) 0))
      all-environments))
  ; first find all the rules that cover as much of the test rule as possible
  (define item-scores (map item-score other-rules))
  (define best-score (apply max item-scores))
  (define contenders (filter-map (λ (r s) (and (= s best-score) r)) other-rules item-scores))
  ; count up how many total cells each contender covers, pick the best of those
  (define total-scores (map total-score contenders))
  (define best-total (apply max total-scores))
  (define finalists (filter-map (λ (r s) (and (= s best-total) r)) contenders total-scores))
  (printf "score: ~a/~a\n" best-score (sum (λ (pr) (length (cdr pr))) items))
  (argmin program-cost finalists))

; returns false for bad work items
(define (verify-par-work _ wr)
  (cond
   [(work-result-success? wr)
    (define prog (ruledata-program (work-result->ruledata wr)))
    (define ce
      (verify-program
        prog
        #:counter-example-parameters (range 1 21)))
    (if ce #f wr)]
   [else wr]))

(define (filter-unsound-rules work-results)
  (define results
    (parallel-map/place
      #:initialize parinit-for-solver
      #:map verify-par-work
      #:finalize parterm-for-solver
      #:list work-results))
  (list (reverse (filter identity results))))

