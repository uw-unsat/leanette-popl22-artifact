#lang racket

; built-in rules, from the Internet.

(provide
  (except-out (all-defined-out) define-builtin builtin-internal-list))

(require
  "../core/core.rkt"
  "ast.rkt"
  "debug.rkt"
  "dsl-pretty.rkt")

(define builtin-internal-list empty)

; name : symbol?
; rule : Program?
; examples: (listof line/fill?)
(standard-struct builtin (name rule examples))

(define-syntax-rule (define-builtin name program examples ...)
  (define name
    (let ([b (builtin 'name program (list examples ...))])
      (set! builtin-internal-list (cons b builtin-internal-list))
      b)))

; Full Hint
; source: Picross 7 (and more) Tutorial
; specialization of Big Hint for hint = row size
(define-builtin rule-full-hint
  (program
    (Singleton 'hint)
    (a= BV N)
    (Fill #t C0 C0 N))
  (make-line/fill '(5) "-----" #t 0 5)
  (make-line/fill '(8) "--------" #t 0 8))

; Full Hint Pair
; source: Picross 7 (and more) Tutorial
; specialization of Big Hint for 2 hints + gap = row size
; in 3 parts because rules can only have one action
(define-builtin rule-full-hint-pair-1
  (program
    (Constant 'hint 0)
    (Constant 'hint 1)
    (a= N (a+ C1 (a+ BV SV)))
    (Fill #t C0 C0 BV))
  (make-line/fill '(3 1) "-----" #t 0 3))

(define-builtin rule-full-hint-pair-2
  (program
    (Constant 'hint 0)
    (Constant 'hint 1)
    (a= N (a+ C1 (a+ BV SV)))
    (Fill #t (a+ C0 (a+ C1 BV)) C0 SV))
  (make-line/fill '(3 1) "-----" #t 4 5))

(define-builtin rule-full-hint-pair-3
  (program
    (Constant 'hint 0)
    (Constant 'hint 1)
    (a= N (a+ C1 (a+ BV SV)))
    (Fill #f C0 BV (a+ C1 BV)))
  (make-line/fill '(3 1) "-----" #f 3 4))

; Big Hint
; source: https://en.wikipedia.org/wiki/Nonogram#Simple_boxes
; This is an infinite family of rules depending on how many hints;
; this is the most general rule, covering all such cases.
(define-builtin rule-big-hint
  (program
    (Arbitrary 'hint)
    (a> (LowestEndCell BI) (HighestStartCell BI))
    (Fill #t C0 (HighestStartCell BI) (LowestEndCell BI)))
  (make-line/fill '(8) "----------" #t 2 8)
  (make-line/fill '(6) "----------" #t 4 6)
  (make-line/fill '(1 8) "----------" #t 0 1)
  (make-line/fill '(1 8) "----------" #t 2 10))

; https://en.wikipedia.org/wiki/Nonogram#Glue
; This is the most general variant of the edge-based version;
; this does not cover rules in the middle of the line.
(define-builtin rule-edge-fill
  (program
    (Constant 'hint 0)
    (Arbitrary 'block)
    (And
      (a> (a- BV C1) (a- SI C0))
      (a> (a+ C0 BV) (a+ SI SV)))
    (Fill #t C0 (a+ SI SV) (a+ C0 BV)))
  (make-line/fill '(6) "--O-------" #t 3 6))

; source: Picross 7 tutorial
(define-builtin rule-full-edge-gap
  (program
    (Constant 'hint 0)
    (Constant 'gap 0)
    (Constant 'block 0)
    (And (a= SI TI) (a> BV C1))
    (Fill #t SI C1 BV))
  (make-line/fill '(4 4) "xxxO-------x--------x" #t 4 7)
  (make-line/fill '(2) "xO---" #t 2 3))

; source: Picross 7 tutorial
; they show the '(2) "-x---" case.
; the following are possible generalizations of this rule
(define-builtin rule-cross-small-gap-singleton
  (program
    (Singleton 'hint)
    (Arbitrary 'gap)
    (a> BV SV)
    (Fill #f SI C0 SV))
  (make-line/fill '(4) "----x---x---" #f 5 8)
  (make-line/fill '(4) "----x---x---" #f 9 12)
  (make-line/fill '(2) "-x---" #f 0 1))

(define-builtin rule-cross-small-gap-min
  (program
    (Arbitrary 'hint)
    (Arbitrary 'gap)
    (And
      (Min? 0)
      (a> BV SV))
    (Fill #f SI C0 SV))
  (make-line/fill '(4) "----x---x---" #f 5 8)
  (make-line/fill '(4) "----x---x---" #f 9 12)
  (make-line/fill '(4 5) "----x---x---------" #f 5 8)
  (make-line/fill '(3 2) "----x----x-x--x--" #f 10 11)
  (make-line/fill '(2) "-x---" #f 0 1))

(define-builtin rule-cross-small-gap-left
  (program
    (Constant 'hint 0)
    (Constant 'gap 0)
    (a> BV SV)
    (Fill #f SI C0 SV))
  (make-line/fill '(3 1) "xx--x----x--" #f 2 4)
  (make-line/fill '(2) "-x---" #f 0 1))

; https://en.wikipedia.org/wiki/Nonogram#Punctuating
; There are many variations of these, we choose a few here.
; Most general version of this that does not require determining hint/block correspondence.
; We don't need a right variant because this can be applied to a flipped board!
; (TODO Maybe we should have one, but ehhhhh).
(define-builtin rule-punctuate-max
  (program
    (Arbitrary 'hint)
    (Arbitrary 'block)
    (And
      (Max? 0)
      (And
        (a= BV SV)
        (a> SI C0)))
    (Fill #f SI CM1 C0))
  (make-line/fill '(1 3) "---OOO----" #f 2 3))

(define-builtin rule-punctuate-hint0
  (program
    (Constant 'hint 0)
    (Constant 'block 0)
    (Constant 'gap 0)
    (And
      (a= BV SV)
      (And
        (a> SI TI)
        (a>= BV (a- SI TI))))
    (Fill #f TI C0 (a- SI TI)))
  (make-line/fill '(4 1) "x---OOOO--" #f 1 4))

; https://en.wikipedia.org/wiki/Nonogram#Mercury
; Also from Picross 7 tutorial.
; There's a version for filling the right as well, we assume covered by symmetric rule application.
(define-builtin rule-mercury
  (program
    (Constant 'hint 0)
    (Constant 'block 0)
    (Constant 'gap 0)
    (And (a> (a+ SI SV) (a+ C0 BV))
         (a>= BV (a- SI C0)))
    (Fill #f C0 C0 (a- (a+ SI SV) BV)))
  (make-line/fill '(4) "----OO----" #f 0 2))

; https://en.wikipedia.org/wiki/Nonogram#Forcing
; this is a subcase of their rules, but state reduction covers the other cases.
; Basically, if there is only gap in which a hint fits, apply a special case of the big hint rule in that gap.
(define-builtin rule-force-max
  (program
    (Arbitrary 'hint)
    (Arbitrary 'gap)
    (And
      (Unique? 1 (a>= (BoundValue) BV))
      (a> (a+ BV BV) SV))
    (Fill #t SI (a- SV BV) BV))
  (make-line/fill '(4 1) "---x----x--" #t 4 8)
  (make-line/fill '(1 4) "---x----x--" #t 4 8)
  (make-line/fill '(3) "x--x----x--" #t 5 7)
  (make-line/fill '(4) "---x----x--" #t 4 8))

;(define-builtin rule-no-hints
;  (program
;    (Arbitrary 'gap)
;    (a= K C0)
;    (Fill #f BI C0 BV))
;  (make-line/fill '() "----------" #f 0 10)
;  (make-line/fill '() "----x-----" #f 0 4)
;  (make-line/fill '() "----x-----" #f 5 10))

(define all-builtin-rules (reverse builtin-internal-list))

