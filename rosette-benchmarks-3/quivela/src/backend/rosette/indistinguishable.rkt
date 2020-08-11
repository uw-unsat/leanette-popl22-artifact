#lang rosette

; Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
; 
; Licensed under the Apache License, Version 2.0 (the "License").
; You may not use this file except in compliance with the License.
; A copy of the License is located at
; 
;     http://www.apache.org/licenses/LICENSE-2.0
; 
; or in the "license" file accompanying this file. This file is distributed 
; on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either 
; express or implied. See the License for the specific language governing 
; permissions and limitations under the License.

(require rosette/lib/angelic racket/hash)
(require "adversary.rkt" "eval.rkt" "print.rkt" "rewrite.rkt" "value.rkt")

(provide Equivalent ValidRewrite AdmitProof 
         DefaultInvariant EquivalenceInvariant OldNewInvariant 
         check-proof check-assert FUEL HavocArg)

(current-bitwidth #f)


(define FUEL (make-parameter 30))


(define (HavocArg var)
  (if (EVar-type var)
      (??Value-typed (EVar-type var))
      (??Value 0 1 #f)))

; Havoc the locals of every object in the context,
; without allowing references to objects beyond maxAddr
(define (HavocContext ctx maxAddr)
  (define new-objs
    (for/list ([a/obj (in-list (Context-objs ctx))])
      (define addr (car a/obj))
      (define immuts (or (assoc-get addr (Context-metadata ctx)) '()))
      (cons addr (Object (for/list ([n/v (in-list (Object-locals (cdr a/obj)))])
                           (if (member (car n/v) immuts)
                               n/v  ; don't havoc immutable fields
                               (cons (car n/v) (??Value (min (car a/obj) maxAddr) 2 #t (cdr n/v)))))))))
  (Context-with-objs ctx new-objs))

; Create a list of symbolic arguments to the given method.
; The arguments cannot be refs or maps.
(define (HavocMethodArgs mtd)
  (for/list ([v (Method-args mtd)]) (HavocArg v)))


; Return a list of the methods common to the objects ctx1[addr1] and ctx2[addr2]
(define (CommonMethods ctx1 ctx2 addr1 addr2)
  (define mtds1 (assoc-get addr1 (Context-methods ctx1)))
  (define mtds2 (assoc-get addr2 (Context-methods ctx2)))
  (for/list ([m mtds1] #:when (and (assoc-get (car m) mtds2)
                                   (equal? (length (Method-args (cdr m)))
                                           (length (Method-args (assoc-get (car m) mtds2))))))
    (cdr m)))


; Call the method named m in the given context
; (use m only for name; must look up method arg names and body explicitly!)
(define (CallMethod m args this ctx)
  (define mtd (assoc-get (Method-name m) (assoc-get this (Context-methods ctx))))
  (define scope (for/list ([n (Method-args mtd)][v args]) (cons (EVar-name n) v)))
  (Call_With_Scope (Method-body mtd) ctx scope this (FUEL)))


(struct Proof (lhs rhs) #:transparent)
(struct RewriteProof Proof (ctx e1 e2 assumptions) #:transparent)
(struct EquivalenceProof Proof (predicate parts methods contexts asserts vacuity?) #:transparent)
(struct MethodProof (predicate method parts values contexts args) #:transparent)
(struct AdmitProof Proof () #:transparent)

(struct Invariant (proc) #:transparent
  #:property prop:procedure (struct-field-index proc))
(struct EquivalenceInvariant Invariant () #:transparent)
(struct OldNewInvariant Invariant () #:transparent)

;; Given two expressions and a context in which to evaluate each,
;; prove that the values returned by the two expressions are equivalent:
;; for all common methods, in all contexts satisfying the invariant,
;; for all arguments, the methods return the same values, and the invariant holds
(define (Equivalent ctx lhs rhs [invs (list (lambda _ #t))] [vacuity? #t])
  (match-define (cons _ ctx0) (Eval ctx (EmptyContext) (FUEL)))
  (match-define (cons ret1 _ctx1) (Eval lhs ctx0 (FUEL)))
  (define ctx0-replay (replay-all-adversaries ctx0))
  (match-define (cons ret2 _ctx2) (Eval rhs ctx0-replay (FUEL)))

  ; fail fast
  (unless (Ref? ret1)
    (error 'Equivalent "LHS does not evaluate to a reference (instead: ~v)" ret1))
  (unless (Ref? ret2)
    (error 'Equivalent "RHS does not evaluate to a reference (instead: ~v)" ret2))

  (define ctx1 (Context-with-ths _ctx1 (Ref-addr ret1)))
  (define ctx2 (Context-with-ths _ctx2 (Ref-addr ret2)))

  (define old-asserts (asserts))

  ; both sides must return references to objects
  (define BothObjects
    (and (Ref? ret1) (ValidRef (Ref-addr ret1) ctx1)
         (Ref? ret2) (ValidRef (Ref-addr ret2) ctx2)))

  ; the invariant must hold in the initial state
  (define invsbase (for/list ([inv invs] #:when (EquivalenceInvariant? inv))
                     (cons inv (inv ctx1 ctx2 (Ref-addr ret1) (Ref-addr ret2)))))
  (define InvariantBase (apply && (map cdr invsbase)))

  ; if we havoc the contexts...
  (define ctx1* (HavocContext ctx1 (Ref-addr ret1)))
  (define ctx2* (HavocContext ctx2 (Ref-addr ret2)))

  ; and the invariant holds before running a method
  (define InvariantInit
    (apply && (for/list ([inv invs] #:when (EquivalenceInvariant? inv))
                          (inv ctx1* ctx2* (Ref-addr ret1) (Ref-addr ret2)))))

  ; then for each method common between the two objects
  (define methods (CommonMethods ctx1 ctx2 (Ref-addr ret1) (Ref-addr ret2)))

  ; for all possible arguments to that method...
  (define MethodProofs
    (for/list ([m methods])
      (define-values (ctx1*-copy ctx2*-copy) (copy-all-adversaries ctx1* ctx2*))
      (let ([args (HavocMethodArgs m)])
        (match-let ([(cons retL ctxL) (CallMethod m args (Ref-addr ret1) ctx1*-copy)]
                    [(cons retR ctxR) (CallMethod m args (Ref-addr ret2) ctx2*-copy)])
          (let ([eqpost (or (equal? retL retR) (and (Error? retL) (Error? retR)))]
                [invspost (for/list ([inv invs] #:when (EquivalenceInvariant? inv)) 
                            (cons inv (inv ctxL ctxR (Ref-addr ret1) (Ref-addr ret2))))]
                [replayed (check-adversary-replays ctxR)])
            (MethodProof (and eqpost (apply && (map cdr invspost)) replayed)
                         m
                         (hash-union
                           (for/hash ([inv invspost])
                             (values (format "invariant ~v is not maintained" (car inv)) (cdr inv)))
                           (hash "return values are not equal" eqpost
                                 "adversary calls differ" replayed))
                         (list retL retR)
                         (list ctxL ctxR)
                         args))))))

  ; aggregate all the preconditions generated by this proof
  ; and remove them from the global context (so they don't appear in later proofs)
  (define new-asserts (asserts))
  (define precondition
    (let* ([delta (- (length new-asserts) (length old-asserts))]
           [new-as (take new-asserts delta)]
           [old-as (drop new-asserts delta)])
      (clear-asserts!)
      (for ([a (reverse old-as)]) (assert a))
      (apply && new-as)))
  
  ; build the actual predicate
  (define pred
    (=> precondition
        (and
         BothObjects
         InvariantBase
         (=> InvariantInit
             (apply && (for/list ([mp MethodProofs]) (MethodProof-predicate mp)))))))

  (define full-pre (and precondition BothObjects InvariantBase InvariantInit))

  ; build the proof parts
  (define parts
    (hash-set
      (for/hash ([inv invsbase])
        (values (format "invariant ~v does not hold in the initial context" (car inv)) (cdr inv)))
      "both sides of a proof must be objects" BothObjects))
  
  (EquivalenceProof lhs rhs pred parts MethodProofs (list ctx1* ctx2*) full-pre vacuity?))


(define (ValidRewrite lhs rhs ctx e1 e2 assumptions)
  (RewriteProof lhs rhs ctx e1 e2 assumptions))


(define (print-context ctx)
  (printf "| this=~v  nextAddr=~v\n" (Context-ths ctx) (Context-nextAddr ctx))
  (for/list ([addr/obj (Context-objs ctx)])
    (match-define (cons addr obj) addr/obj)
    (define mtds (assoc-get addr (Context-methods ctx)))
    (if (adversary? mtds)
        (printf "| * object ~v [adversary trace: ~a]\n" addr (adversary->history-string mtds))
        (let ([mtdlist (map car mtds)])
          (if (> addr 0)
              (printf "| * object ~v [methods: ~a]\n" addr (string-join (map ~a mtdlist) " "))
              (printf "| * globals\n"))
          (for/list ([l/v (Object-locals obj)])
            (printf "|   * ~v = ~a\n" (car l/v) (value-to-string (cdr l/v))))))))

(define (check-equivalence-proof p)
  (match-define (EquivalenceProof e1 e2 pred parts methods contexts precond vacuity?) p)
  (define m (complete-solution (verify (assert pred)) (symbolics p)))
  (cond
    [(sat? m)
     (define (failure)
       (printf "\ncould not prove equivalence. counterexample:\n")
       (for ([(c i) (in-indexed contexts)])
         (printf "| context ~v:\n" i)
         ;(pretty-print (evaluate c m))
         (print-context (evaluate c m)))
       (for ([(name p) parts])
         (unless (evaluate p m)
           (printf "* ~a\n" name)))
       (for ([mp methods])
         (match-define (MethodProof predicate method parts values mtd-contexts args) mp)
         (unless (evaluate predicate m)
           (parameterize ([print-errors? #t])
             (printf "method ~a(~a):\n" (Method-name method) (string-join (map value-to-string (evaluate args m)) ", "))
             (printf "* LHS returns ~a\n* RHS returns ~a\n"
                     (value-to-string (evaluate (car values) m))
                     (value-to-string (evaluate (cadr values) m)))
             (printf "| LHS context:\n")
             (print-context (evaluate (car mtd-contexts) m))
             ;(pretty-print (evaluate (car mtd-contexts) m))
             (printf "| RHS context:\n")
             (print-context (evaluate (cadr mtd-contexts) m))
             ;(pretty-print (evaluate (cadr mtd-contexts) m))
             (for ([(name p) parts])
               (unless (evaluate p m)
                 (printf "* ~a\n" name)))))))
     (values #f failure)]
    [vacuity?
     (define pre (apply && (for/list ([(_ p) (in-hash parts)]) p)))
     (define method-vacuity
       (for/list ([mp methods])
         (define retL (car (MethodProof-values mp)))
         (define retR (cadr (MethodProof-values mp)))
         (define vac? (solve (assert (and precond (not (Error? retL))))))
         (define m_vac (complete-solution vac? (symbolics mp)))
         (if (sat? m_vac)
             (cons (evaluate retL m_vac) (evaluate (MethodProof-args mp) m_vac))
             m_vac)))
     (define (success)
       (printf "equivalent on methods:\n")
       (for ([mp methods][mv method-vacuity])
         (match-define (MethodProof _ method _ _ _ _) mp)
         (if (solution? mv)
             (printf "* ~a (NO GOOD RETURN VALUE?)\n" (Method-name method))
             (let ([name (Method-name method)]
                   [ret (value-to-string (car mv))]
                   [args (string-join (map value-to-string (cdr mv)) ", ")])
               (printf "* ~a (possible return: ~a(~a) = ~a)\n" name name args ret)))))
     (values #t success)]
    [else
     (define (success)
       (printf "equivalent on methods: ")
       (for ([mp methods])
         (printf "~v " (Method-name (MethodProof-method mp))))
       (printf "\n"))
     (values #t success)]))

(define (check-rewrite-proof p)
  ; lhs, rhs are the goals
  ; e1, e2 are the substitutions
  ; we want to check lhs[e1 := e2] == rhs
  (match-define (RewriteProof lhs rhs ctx e1 e2 assumptions) p)
  (define is-assumed-pair
    (for/or ([pair assumptions])
      (and (equal? (car pair) e1)
           (equal? (cdr pair) e2))))
  (cond
    [is-assumed-pair
     ; rewrite the lhs
     (define lhs-rewrite (rewrite-expr lhs e1 e2))
     (cond
       [(equal? lhs-rewrite rhs)
        (values #t (thunk (printf "replaced ~a with ~a\n" (expr-to-string e1) (expr-to-string e2))))]
       [else
        (values #f (thunk (printf "substitution did not succeed\n")
                          (printf "LHS after substitution:\n")
                          (print-expr lhs-rewrite)
                          (printf "\nRHS:\n")
                          (print-expr rhs)))])]
    [else
     (values #f (thunk (printf "no proof of ~a ~~ ~a found\n" (expr-to-string e1) (expr-to-string e2))))]))

(define (check-admit-proof p)
  (values #t (thunk (printf "(admitted)\n"))))

(define (check-proof proof)
  (match-define (Proof lhs rhs) proof)
  (define checker
    (cond
      [(EquivalenceProof? proof)
       check-equivalence-proof]
      [(RewriteProof? proof)
       check-rewrite-proof]
      [(AdmitProof? proof)
       check-admit-proof]
      [else
       (error 'check-proof "unknown proof ~v" proof)]))
  (define-values (succ ret) (checker proof))
  (if succ
      (let ()
        (printf "\nProved:\n  ")(print-expr lhs)(printf "\n~~\n  ")(print-expr rhs)(printf "\n")
        (ret)
        (printf "\n"))
      (let ()
        (printf "\nFAILED:\n  ")(print-expr lhs)(printf "\n~~\n  ")(print-expr rhs)(printf "\n")
        (ret)
        (printf "\n")
        (exit 1)))
  (flush-output))


(define (check-assert a)
  (define m (verify (assert a)))
  (when (sat? m)
    (error "assert failed")))


; A default invariant that requires all common fields to be equal
(define DefaultInvariant
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define locals1 (Object-locals (assoc-get addr1 (Context-objs ctx1))))
    (define locals2 (Object-locals (assoc-get addr2 (Context-objs ctx2))))
    (for*/all ([locals1 locals1][locals2 locals2])
      (apply && (for/list ([k/v locals1])
                  (=> (not (false? (assoc-get (car k/v) locals2)))
                      (equal? (cdr k/v) (assoc-get (car k/v) locals2)))))))))
