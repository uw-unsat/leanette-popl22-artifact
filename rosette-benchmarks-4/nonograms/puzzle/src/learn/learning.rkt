#lang rosette

(provide
  (struct-out learning-config)
  (struct-out work-item)
  (struct-out work-result)
  (struct-out ruledata)
  work-result-success?
  work-result-failure?
  work-result-input
  work-result-delta
  work-result->ruledata
  work-items-for-transition
  builtin->ruledata
  make-learning-config
  learn-rule
  learn-rule-family
  learn-general-pattern
  make-work-items
  run-rule-learner-on-items
  )

(require
  "../core/core.rkt"
  "../nonograms/nonograms.rkt"
  "../nonograms/dsl-pretty.rkt"
  (only-in "../nonograms/builtin.rkt" builtin)
  "cegis.rkt"
  "synthesize.rkt")

(standard-struct learning-config (ce-params fp-params max-bindings gs-params max-sketch-depth feature-set timeout))
(define (make-learning-config
          #:counter-example-parameters ce-params
          #:force-positive-parameters fp-params
          #:max-binding-count max-bindings
          ; #f | (listof integer?), generalization is disabled if #f
          #:generalization-set-parameters gs-params
          #:max-sketch-depth [max-sketch-depth (current-max-sketch-depth)]
          #:feature-set [feature-set (current-sketch-features)]
          #:timeout [timeout 300])
  ; catch the potential 'null value of gs-params
  (learning-config ce-params fp-params max-bindings (and (list? gs-params) gs-params) max-sketch-depth feature-set timeout))

(standard-struct work-item (transition binding action))

; item : work-item? - the item being processed
; program: (or/c false? Program?) - the synthesized program (if any)
; stage: symbol? - the state at which the process was stopped.
(standard-struct work-result (stage item program))
; Did we find a valid program?
(define (work-result-success? wr) (not (not (work-result-program wr))))
; Should we have found a program but we did not?
; This is not the same as not finding a valid program---
; if we determine no such rule can exist during precheck, that is okay.
(define (work-result-failure? wr) (not (or (work-result-program wr) (equal? (work-result-stage wr) 'precheck))))
(define (work-result-input wr) (work-item-transition (work-result-item wr)))
(define (work-result-delta wr)
  (define wrkitm (work-result-item wr))
  (define ctx (line-transition-start (work-item-transition wrkitm)))
  (define actn (work-item-action wrkitm))
  (line/fill ctx actn))

(standard-struct ruledata (program examples meta))
(define (work-result->ruledata wr)
  (ruledata (work-result-program wr) (list (work-result-delta wr)) (work-result-stage wr)))

(define (builtin->ruledata b)
  (match-define (builtin n p e) b)
  (ruledata p e 'n/a))

; line-transition? -> work-item?
(define (work-items-for-transition tctx #:max-binding-size max-binding-size)
  ; create a work item for each binding up to a potential size
  (define all-patterns (most-specific-patterns-of-line (line-transition-start tctx)))
  (define possible-patterns (choices-up-to all-patterns max-binding-size))
  ; use largest contiguous filled regions for possible actions, synthesizer can make them cover filling already-filled cells if necessary.
  ; this isn't technically complete, we could be overfilling, but ehhhhhhh.
  (define possible-outputs (transition->fills tctx))
  ; now smash them together in every possible way
  (for*/list ([b possible-patterns]
              [o possible-outputs])
    (work-item tctx b o)))

(define (learn-rule cfg wrkitm)
  (parameterize ([current-max-sketch-depth (learning-config-max-sketch-depth cfg)])
    (dprintf "learning rule for ~s" wrkitm)
    (match-define (work-item tctx bnding actn) wrkitm)
    (define stage 'initial)
    (define (receive-notification item)
      (set! stage
        (match item
         [(list 'optimization-started  (synthesis-objective-function 'generalization _ _)) 'generalization-start]
         [(list 'optimization-finished (synthesis-objective-function 'generalization _ _)) 'generalization-finish]
         [(list 'optimization-started  (synthesis-objective-function 'cost _ _)) 'cost-start]
         [(list 'optimization-finished (synthesis-objective-function 'cost _ _)) 'final])))
    (define synthesized (time
      (run-with-timeout/eater (learning-config-timeout cfg) #f
        (λ (eat)
          (if (learning-config-gs-params cfg)
              (synthesize-program
                #:input (line-transition-start tctx)
                #:output actn
                #:binding bnding
                #:counter-example-parameters (learning-config-ce-params cfg)
                #:generalization-set-parameters (learning-config-gs-params cfg)
                #:program-eater eat
                #:optimization-state-update receive-notification
                )
              (synthesize-program/no-generalization
                #:input (line-transition-start tctx)
                #:output actn
                #:binding bnding
                #:counter-example-parameters (learning-config-ce-params cfg)
                #:program-eater eat
                #:optimization-state-update receive-notification
                ))))))
    (cond
     [synthesized
      ; if we were generalizing, re-optimize the cost because we probably timed out during generalization.
      (define optimized
        (or
          (and
            (learning-config-gs-params cfg)
            (run-with-timeout/eater 60 #f
              (λ (eat)
                (superoptimize-program
                  #:primary-input (line-transition-start tctx)
                  #:primary-output actn
                  #:program synthesized
                  #:counter-example-parameters (learning-config-ce-params cfg)
                  #:program-eater eat))))
          synthesized))
      (unless optimized (error (format "something wrong! synthesis succeeded but superoptimization failed! ~s" (serialize wrkitm))))
      (dprintf "SUCCESS: ~a" (debug-format-program optimized))
      (work-result stage wrkitm optimized)]
     [else
      (dprintf "FAILURE")
      ;(if (potential-program-exists? tctx actn bnding)
          ;(work-result 'precheck wrkitm #f)
          (work-result stage wrkitm #f)])))

; learn a rule for this work item and all bindings higher on the binding lattice
(define (learn-rule-family cfg wrkitm)
  (collect-garbage)
  (match-define (work-item tctx base-binding actn) wrkitm)
  (define grph (build-pattern-graph base-binding))
  (define rev-grph (dg-reverse-edges grph))
  (define result-map (make-hasheq)) ; binding? -> work-result?
  (define (do-work node)
    (define binding (dg-node-value node))
    ; only bother doing the work if all incoming neighbors terminated successfully
    (when
      (andmap
        (λ (n)
          (define r (hash-ref result-map (dg-node-value n) #f))
          ; heuristic: only do the next rule if the previous actually used all the bindings somehow.
          (and r (work-result-success? r) (program-uses-all-bindings? (work-result-program r))))
        (dg-outgoing-neighbors (dg-node-ref rev-grph binding)))
      (hash-set! result-map binding (learn-rule cfg (work-item tctx binding actn)))))
  (define nodes (dg-topological-sort grph))
  (for-each do-work nodes)
  ; output in toplogical order
  (filter-map (λ (n) (hash-ref result-map (dg-node-value n) #f)) nodes))

; learn a rule for this work item and all bindings higher on the binding lattice
(define (learn-general-pattern f base-pattern)
  (define grph (build-pattern-graph base-pattern))
  (define rev-grph (dg-reverse-edges grph))
  (define result-map (make-hasheq)) ; pattern? -> work-result?
  (define (do-work node)
    (define pattern (dg-node-value node))
    ; only bother doing the work if all incoming neighbors terminated successfully
    (when
      (andmap
        (λ (n)
          (define r (hash-ref result-map (dg-node-value n) #f))
          ; heuristic: only do the next rule if the previous actually used all the patterns somehow.
          (and r (work-result-success? r) (program-uses-all-bindings? (work-result-program r))))
        (dg-outgoing-neighbors (dg-node-ref rev-grph pattern)))
      (hash-set! result-map pattern (f pattern))))
  (define nodes (dg-topological-sort grph))
  (for-each do-work nodes)
  ; output in toplogical order
  (filter-map (λ (n) (hash-ref result-map (dg-node-value n) #f)) nodes))

(define (make-work-items starting-transitions parameter-config)
  (append-map (λ (t) (work-items-for-transition t #:max-binding-size (learning-config-max-bindings parameter-config))) starting-transitions))

(define (run-rule-learner-on-items parameter-config work-items)
  (map
    (curry learn-rule-family parameter-config)
    work-items))

