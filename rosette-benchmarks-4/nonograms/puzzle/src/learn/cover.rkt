#lang rosette/safe

; implementation of minimum set cover in rosette

(provide
  find-minimum-set-cover
  find-minimum-weak-cover-for-conjunctions
  find-greedy-minimum-weak-cover-for-conjunctions
  find-minimum-weak-cover-for-graph
  )

(require
  "../core/core.rkt"
  "cegis.rkt"
  (only-in racket parameterize hash-copy remove-duplicates for error values for/list set-member? in-set set-remove set-count list->seteq set->list build-vector make-hasheq hash-ref)
  rosette/lib/match
  rosette/lib/angelic
  rosette/solver/smt/z3)

; 'a list list -> boolean? list
; given a sequence of sets, finds the minimum number of them that covers the union of all the sets.
(define (find-minimum-set-cover sets)
  (parameterize-solver
    (define universe (remove-duplicates (apply append sets)))
    (define setvec (list->vector sets))
    (define chosen? (map (λ (_) (!!)) sets))
    (define chosen?-vec (list->vector chosen?))
    (define num-chosen (count identity chosen?))
    (define sets-of-item
      (map
        (λ (x) (map (curry vector-ref chosen?-vec) (filter (λ (i) (member x (vector-ref setvec i))) (range/s 0 (length sets)))))
        universe))
    (define constrs
      (map
        (λ (s) (ormap identity s))
        sets-of-item))
    (define soln
      (optimize
        #:minimize (list num-chosen)
        #:guarantee (for ([c constrs]) (assert c))))
    (and (sat? soln) (evaluate chosen? soln))))


; Given a sequence of items (as a list of elements) that are covered only if each of those elements is in the cover set,
; find the minimum such cover set such that at most max-elements are used.
; Note that this input is totally backwards from find-minimum-set-cover:
; that one passes elements as a list of covered items, this passes in a list of items as which conjunction of elements cover them.
; The previous only requires one element per item, this requires a conjunction.
(define (find-minimum-weak-cover-for-conjunctions elements-for-item max-elements)
  (define pr
    (parameterize-solver
      (define elements (remove-duplicates (apply append elements-for-item)))
      (define chosen? (map (λ (_) (!!)) elements))
      (define chosen?-vec (list->vector chosen?))
      (define num-chosen (count identity chosen?))
      (define covered-items
        (map
          (λ (elements) (&&map (λ (i) (vector-ref chosen?-vec i)) elements))
          elements-for-item))
      (define num-covered
        (count identity covered-items))
      (define soln
        (optimize
          #:maximize (list num-covered)
          #:guarantee (assert (<= num-chosen max-elements))))
      (unless (sat? soln) (error "no weak cover!"))
      (cons
        (evaluate chosen? soln)
        (evaluate num-covered soln))))
  ; my macro is too naive to deal with values correctly
  (values (car pr) (cdr pr)))

(define (all-drop-one st)
  (for/list ([s (in-set st)])
    (cons s (set-remove st s))))

; same as find-minimum-weak-cover-for-conjunctions, only using a greedy non-optimal algorithm.
; but it will actually terminate quickly instead of taking multiple days.
(define (find-greedy-minimum-weak-cover-for-conjunctions elements-for-item max-elements)
  (define elements (remove-duplicates (apply append elements-for-item)))
  (define (covered-items pair)
    (define selected (cdr pair))
    (define chosen? (list->vector (map (curry set-member? selected) elements)))
    (count
      (λ (elems) (andmap (λ (i) (vector-ref chosen? i)) elems))
      elements-for-item))
  (define result
    (let loop ([remaining (list->seteq elements)])
      ; once we're down to max-elements, stop
      (cond
       [(>= max-elements (set-count remaining))
        remaining]
       [else
        ; try to leave one out, choose the best
        (define candidates (all-drop-one remaining))
        (define selected (argmax covered-items candidates))
        (loop (cdr selected))])))
  (values
    (set->list result)
    (covered-items (cons #f result))))

(define (nested-map f list-of-lists)
  (map
    (λ (lst) (map f lst))
    list-of-lists))

; (listof digraph?), integer? -> (listof integer?)
(define (find-minimum-weak-cover-for-graph items max-elements)
  ; flip all the graphs, we need the edges going the other way
  (define graphs (map dg-reverse-edges items))
  ; the nodes we are trying to reach
  (define goals (append-map dg-sources graphs))
  ; filter paths for those with no impossible edge
  (define paths
    (map
      (λ (nde)
        (filter-not
          (λ (p) (ormap empty? p))
          (dg-all-reverse-paths nde)))
      goals))
  (define all-edges (append-map dg-edge-values graphs))
  (define max-element (apply max (apply append all-edges)))
  ; creating mapping from edges to integers. Assume all lists are distinct so we can just use eq?
  ; the null lists don't matter (we filter them out anyway) so it's okay that they are eq?
  (define edge->index (make-hasheq (map cons all-edges (range/s 0 (length all-edges)))))

  (parameterize-solver-bw 12
    ; the graph edges we choose to select
    (define selected-edges (build-vector (length all-edges) (λ (_) (!!))))
    ; the portions of the transitions that we are covering
    (define selected-goals (map (λ (_) (??* 0 2)) goals))
    ; the rules we are choosing to use
    (define selected-elements (build-vector (add1 max-element) (λ (_) (!!))))
    (define score (apply + selected-goals))

    ; ensure our variables are aligned properly
    (define (make-asserts)
      (assert (<= (count identity (vector->list selected-elements)) max-elements))
      ; if an edge is selected, then we better have had selected at least one of its elements
      (for ([edge-value all-edges]
            [edge-selected? selected-edges])
        (assert (<=> edge-selected? (lormap (λ (i) (vector-ref selected-elements i)) edge-value))))

      ; if a goal is selected, then we better have had selected at least one path (all edges along the path)
      (for ([possible-paths paths]
            [goal-score selected-goals])
        (assert
          (<=>
            (> goal-score 0)
            (lormap
              (λ (path)
                (&&map (λ (e) (vector-ref selected-edges (hash-ref edge->index e))) path))
              possible-paths)))))

    (define soln
      (optimize
        #:maximize (list score)
        #:guarantee (make-asserts)))

    (unless (sat? soln) (error "no weak cover!"))
    (dprintf "coverage: ~a" (evaluate score soln))
    (filter-mapi (λ (i b) (and b i)) (vector->list (evaluate selected-elements soln)))))


; items : (listof digraph?)
(define (find-greedy-minimum-weak-cover-for-graph** items max-elements)
  ; flip all the graphs, we need the edges going the other way
  (define graphs (map dg-reverse-edges items))
  (define all-edges (append-map dg-edge-values graphs))

  ; creating mapping from edges to integers. Assume all lists are distinct so we can just use eq?
  ; the null lists don't matter (we filter them out anyway) so it's okay that they are eq?
  (define edge->index (make-hasheq (map cons all-edges (range/s 0 (length all-edges)))))

  (parameterize-solver
    (parameterize ([current-bitwidth 12])
      (define max-element (apply max (apply append all-edges)))
      (define elements-vec (build-vector (add1 max-element) (λ (_) (!!))))
      (define edges-vec (build-vector (length all-edges) (λ (_) (!!))))
      (define (element-selected? i) (vector-ref elements-vec i))
      (define (edge-selected? i) (vector-ref edges-vec i))
      (define (path-selected? p) (&&map (λ (e) (edge-selected? (hash-ref edge->index e))) p))
      (define (item-covered? grph)
        (dprintf "grph: ~a" grph)
        (define sources (dg-sources grph))
        ; TODO need a score function that maps sources covered to total coverage of graph
        ; prune paths that are impossible (they have at least one edge with no paths)
        (dprintf "sources: ~a" sources)
        (define possible-paths
          (filter-not
            (λ (p) (ormap empty? p))
            (append-map dg-all-reverse-paths sources)))
        (dprintf "possible: ~a" possible-paths)
        (lormap path-selected? possible-paths))
      (define chosen-count (count item-covered? items))
      (define soln
        (optimize
          #:maximize (list chosen-count)
          #:guarantee
            (let ()
              (for ([i (length all-edges)]
                    [e all-edges])
                (assert (<=> (edge-selected? i) (lormap element-selected? e))))
              (assert (>= max-elements (count identity (vector->list elements-vec)))))))
      (unless (sat? soln) (error "no weak cover!"))
      (dprintf "coverage: ~a" (evaluate chosen-count soln))
      (filter-mapi (λ (i b) (and b i)) (vector->list (evaluate elements-vec soln))))))

(define (find-greedy-minimum-weak-cover-for-graph* items max-elements)
  ; flip all the graphs, we need the edges going the other way
  (define graphs (map dg-reverse-edges items))
  (define all-edges (append-map dg-edge-values graphs))

  ; creating mapping from edges to integers. Assume all lists are distinct so we can just use eq?
  ; the null lists don't matter (we filter them out anyway) so it's okay that they are eq?
  (define edge->index (make-hasheq (map cons all-edges (range/s 0 (length all-edges)))))
  (define max-element (apply max (apply append all-edges)))

  (parameterize-solver
    (parameterize ([current-bitwidth 12])
      (define slvr (current-solver))
      (solver-clear slvr)

      (define elements-vec (build-vector (add1 max-element) (λ (_) (!!))))
      (define edges-vec (build-vector (length all-edges) (λ (_) (!!))))
      (define (element-selected? i) (vector-ref elements-vec i))
      (define (edge-selected? i) (vector-ref edges-vec i))
      (define (path-selected? p) (&&map (λ (e) (edge-selected? (hash-ref edge->index e))) p))
      (define (item-covered? grph)
        (dprintf "grph: ~a" grph)
        (define sources (dg-sources grph))
        ; TODO need a score function that maps sources covered to total coverage of graph
        ; prune paths that are impossible (they have at least one edge with no paths)
        (dprintf "sources: ~a" sources)
        (define possible-paths
          (filter-not
            (λ (p) (ormap empty? p))
            (append-map dg-all-reverse-paths sources)))
        (dprintf "possible: ~a" possible-paths)
        (lormap path-selected? possible-paths))

      (define chosen-count (eval-with-solver slvr (count item-covered? items)))

      (define obj
        (synthesis-objective-function
          'coverage
          (λ (soln)
            (define c (arbitrary-concretization (evaluate chosen-count soln)))
            (dprintf "trying to increase coverage above ~a" c)
            (solver-assert* slvr (> chosen-count c)))
          (λ (_) #f)))


      (let ()
        (for ([i (length all-edges)]
              [e all-edges])
          (solver-assert* slvr (<=> (edge-selected? i) (lormap element-selected? e))))
        (solver-assert* slvr (>= max-elements (count identity (vector->list elements-vec)))))

      (define (do-solve)
        (define s (solver-check slvr))
        (and (sat? s) s))

      (define soln
        (run-incremental-optimization
          slvr
          do-solve
          (list obj)))

      (unless (sat? soln) (error "no weak cover!"))
      (dprintf "coverage: ~a" (evaluate chosen-count soln))
      (filter-mapi (λ (i b) (and b i)) (vector->list (evaluate elements-vec soln))))))

