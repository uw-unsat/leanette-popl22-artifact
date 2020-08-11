#lang rosette

(require (file "src/backend/rosette/eval.rkt"))
(require (file "src/backend/rosette/indistinguishable.rkt"))
(require (file "src/backend/rosette/print.rkt"))

(FUEL 10)

(define equal_invariant0
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'count (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'ctr (EConst (Nil))) 'count (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent0)
  (define ctx0 (ESeq (EMethod 'Ctr (list ) (ENew (list (Init 'count (EConst (Int 0)) #f)) (ESeq (EMethod 'inc (list (EVar 'x)) (EAssign (EVar 'count) (ECall (EConst (Nil)) '+ (list (EVar 'count) (EVar 'x))))) (EMethod 'get (list ) (EVar 'count))))) (EMethod 'CtrDelegate (list (EVar 'ctr)) (ENew (list (Init 'ctr (EConst (Nil)) #f)) (ESeq (EMethod 'inc (list (EVar 'x)) (ECall (EVar 'ctr) 'inc (list (EVar 'x)))) (EMethod 'get (list ) (ECall (EVar 'ctr) 'get (list ))))))))
  (define lhs0 (ECall (EConst (Nil)) 'Ctr (list )))
  (define rhs0 (ECall (EConst (Nil)) 'CtrDelegate (list (ECall (EConst (Nil)) 'Ctr (list )))))
  (define invariants (list equal_invariant0))
  (check-proof (Equivalent ctx0 lhs0 rhs0 invariants)))

(time (equivalent0))