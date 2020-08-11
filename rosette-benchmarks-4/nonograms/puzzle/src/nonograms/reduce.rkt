#lang rosette/safe

(provide
  (struct-out subspace-mapping)
  identity-subspace-mapping
  compose-subspace-mappings
  apply-subspace-mapping
  apply-subspace-mapping-t
  reverse-subspace-mapping
  reverse-subspace-mapping-a
  (prefix-out subspace- split-ok?)
  find-subspace-mappings)

(require
  (only-in racket match-define match-let* for error)
  "../core/core.rkt"
  "rules.rkt"
  "bindings.rkt"
  "action.rkt"
  "symbolic.rkt")

(standard-struct subspace-mapping (hint-range cell-range))

(define (identity-subspace-mapping ctx)
  (match-define (line hints cells) ctx)
  (subspace-mapping (cons 0 (length hints)) (cons 0 (length cells))))

; composes two subspace mappings such that the results applies the right first and the left second.
(define (compose-subspace-mappings sm1 sm2)
  (match-define (subspace-mapping (cons hs1 he1) (cons cs1 ce1)) sm1)
  (match-define (subspace-mapping (cons hs2 he2) (cons cs2 ce2)) sm2)
  (subspace-mapping
    (cons (+ hs1 hs2) (+ he1 hs2))
    (cons (+ cs1 cs2) (+ ce1 cs2))))

; subspace-mapping?, line? -> line?
(define (apply-subspace-mapping sm ctx)
  (match-define (subspace-mapping hint-range cell-range) sm)
  (match-define (line hints cells) ctx)
  (line (slice* hints hint-range) (slice* cells cell-range)))

; subspace-mapping?, line-transition? -> line-transition?
(define (apply-subspace-mapping-t sm tctx)
  (match-define (subspace-mapping hint-range cell-range) sm)
  (match-define (line-transition (line hints start) end) tctx)
  (line-transition (line (slice* hints hint-range) (slice* start cell-range)) (slice* end cell-range)))

(define (set-slice lst range vals)
  (match-define (cons start end) range)
  (define head (take lst start))
  (define tail (drop lst end))
  (append head (append vals tail)))

; subspace-mapping?, line?, line? -> line?
(define (reverse-subspace-mapping sm original sub)
  (match-define (subspace-mapping hint-range cell-range) sm)
  (match-define (line hints0 cells0) original)
  (match-define (line hints1 cells1) sub)
  (line
    (set-slice hints0 hint-range hints1)
    (set-slice cells0 cell-range cells1)))

; subspace-mapping?, fill-action? -> fill-action?
(define (reverse-subspace-mapping-a sm actn)
  (match-define (subspace-mapping _ (cons s _)) sm)
  (match-define (fill-action val start end) actn)
  (fill-action val (+ start s) (+ end s)))

(struct bound-hint (hint block) #:transparent)

; line? -> line?
; fill in the line with an arbitrary (but valid) solution.
(define (arbitrary-solution-for start-ctx)
  (define (f checker end-ctx segments)
    (define soln (solver-check checker))
    (and (sat? soln) (evaluate segments soln)))
  (solve-with-symbolic-deduction f start-ctx))

(define (split-ok? ctx hint-index cell-index)
  (define (f checker end-ctx segments)
    (define left-seg (list-ref segments (sub1 hint-index)))
    (define right-seg (list-ref segments hint-index))
    (solver-assert* checker
      (||
        (> (segment-end left-seg) cell-index)
        (<= (segment-start right-seg) cell-index)))
    (define soln (solver-check checker))
    ;(when (sat? soln)
    ;  (printf "counter ex: ~a\n" (evaluate end-ctx soln)))
    (unsat? soln))
  (solve-with-symbolic-deduction f ctx))

; line?, (listof segment?) integer? -> (or/c #f integer?)
(define (find-split-between-hints ctx solution-segments hint-index)
  ; grab any solution as a starting point
  (define guess-cell-index (sub1 (segment-start (list-ref solution-segments hint-index))))
  (and
    (split-ok? ctx hint-index guess-cell-index)
    (let loop ([last-guess guess-cell-index])
      (cond
       [(split-ok? ctx hint-index (sub1 last-guess))
        (loop (sub1 last-guess))]
       [else (cons hint-index last-guess)]))))

(define (hint-bound-to-block? start-ctx pr)
  (match-define (bound-hint (cons hidx hval) to-check) pr)
  (define (f checker end-ctx segments)
    (define seg (list-ref segments hidx))
    ; try to find a solution which does NOT have this segment as part of the hidx'th segment
    (solver-assert* checker (not (segment-subset? to-check seg)))
    (define soln (solver-check checker))
    ; if we fail, then they are bound
    (unsat? soln))
  (solve-with-symbolic-deduction f start-ctx))

; line? -> (listof subspace-mapping?)
(define (find-subspace-mappings ctx)
  ; identity all necessarily-bound hint-block pairs
  (define splits
    (let ()
      ; first make any guess to the filled line, use this for hypotheses of bound hints
      (define hints (mapi cons (line-hints ctx)))
      (cond
       [(<= (length hints) 1)
        empty]
       [else
        (define guess-solution (arbitrary-solution-for ctx))
        (unless guess-solution
          (error (format "something wrong! ~a didn't have a solution!\n" ctx)))
        ; guess a split for any hint (except the first)
        (filter-map (curry find-split-between-hints ctx guess-solution) (range/s 1 (length hints)))])))
  ;(printf "splits: ~a\n" splits)

  ; split state between each of these into slices
  (cond
   [(empty? splits) empty]
   [else
    ; we have a subspace on the left if the left-most hint is satisified
    (define left-sub
      (match-let* ([(cons hidx cidx) (first splits)])
        (subspace-mapping (cons 0 hidx) (cons 0 cidx))))
    ; we have a subspace on the right if the right-most hint is satisified
    (define right-sub
      (match-let* ([(cons hidx cidx) (last splits)]
                   [K (length (line-hints ctx))]
                   [N (length (line-cells ctx))])
        (subspace-mapping (cons hidx K) (cons (add1 cidx) N))))
    (define center-subs
      (map
        (λ (pr)
          (match-define (cons (cons hidx0 cidx0) (cons hidx1 cidx1)) pr)
          (subspace-mapping
            (cons hidx0 hidx1)
            (cons (add1 cidx0) cidx1)))
        (sequential-pairs splits)))

    (define potential (cons left-sub (append center-subs (list right-sub))))
    ; only return subspaces with empty cells in them
    (filter
      (λ (sm)
        (ormap empty-cell? (line-cells (apply-subspace-mapping sm ctx))))
      potential)]))

