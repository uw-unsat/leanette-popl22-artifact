#lang rosette

(require (file "src/backend/rosette/eval.rkt"))
(require (file "src/backend/rosette/indistinguishable.rkt"))
(require (file "src/backend/rosette/print.rkt"))

(define equal_invariant0
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant1
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent0)
  (define ctx0 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs0 (ECall (EConst (Nil)) 'EtM (list (EVar '_e) (EVar '_mac))))
  (define rhs0 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (EVar '_mac) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))
  (define invariants (list equal_invariant0 equal_invariant1))
  (check-proof (Equivalent ctx0 lhs0 rhs0 invariants)))

(define (validrewrite0)
  (define ctx3 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs1 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (EVar '_mac) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))
  (define rhs1 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))
  (define assumptions0 (list(cons (EVar '_e) (ECall (EConst (Nil)) 'Enc (list (EVar '_e)))) (cons (ECall (EConst (Nil)) 'CpaC (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaI (list (EVar '_e)))) (cons (EVar '_mac) (ECall (EConst (Nil)) 'MacI (list (EVar '_mac)))) (cons (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) (EVar '_e)) (cons (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaC (list (EVar '_e)))) (cons (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) (EVar '_mac))))
  (check-proof (ValidRewrite lhs1 rhs1 ctx3 (EVar '_mac) (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) assumptions0)))

(define equal_invariant2
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant3
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant4
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant5
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent1)
  (define ctx4 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs2 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))
  (define rhs2 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ENew (list (Init 'e (EVar '_e) #t)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))
  (define invariants (list equal_invariant2 equal_invariant3 equal_invariant4 equal_invariant5))
  (check-proof (Equivalent ctx4 lhs2 rhs2 invariants)))

(define equal_invariant6
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant7
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define ref_invariant0
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx1 addr1))
    (match-define (cons ret _) (Eval (EVar 'e) ctx))
    (Ref? ret))))

(define equal_invariant8
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant9
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant10
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant11
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant12
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent2)
  (define ctx7 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs3 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ENew (list (Init 'e (EVar '_e) #t)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))
  (define rhs3 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ENew (list (Init 'e (EVar '_e) #t)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define invariants (list equal_invariant6 equal_invariant7 ref_invariant0 equal_invariant8 equal_invariant9 equal_invariant10 equal_invariant11 equal_invariant12))
  (check-proof (Equivalent ctx7 lhs3 rhs3 invariants)))

(define equal_invariant13
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant14
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant15
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant16
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant17
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant18
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant19
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent3)
  (define ctx10 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs4 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ENew (list (Init 'e (EVar '_e) #t)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define rhs4 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ENew (list (Init 'e (EVar '_e) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))) #t)) (ESeq (EMethod 'enc (list (EVar 'a 'value) (EVar 'm 'value)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a 'value) (EVar 'c (list 'value 'value))) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define invariants (list equal_invariant13 equal_invariant14 equal_invariant15 equal_invariant16 equal_invariant17 equal_invariant18 equal_invariant19))
  (check-proof (Equivalent ctx10 lhs4 rhs4 invariants)))

(define args0 (list (EVar 'a 'value) (EVar 'em 'value)))
(define scope0 (for/list ([v args0]) (cons (EVar-name v) (HavocArg v))))

(define invariant0
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define body (ECall (EConst (Nil)) '|| (list (ECall (EConst (Nil)) '! (list (ECVar (EVar 'mac) 'tg (ETuple (list (EVar 'a) (EVar 'em)))))) (ECVar (EVar 'cpa) 'h (EVar 'em)))))
    (define qvs (symbolics scope0))
    (match-define (cons retL _) (Call_With_Scope body ctx1 scope0 addr1 (FUEL)))
    (match-define (cons retR _) (Call_With_Scope body ctx2 scope0 addr2 (FUEL)))
    (forall qvs (and (not (Error? retL)) (not (Error? retR)))))))

(define equal_invariant20
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant21
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant22
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant23
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define valid_invariant0
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx1 addr1))
    (match-define (cons ret _) (Eval (ECVar (EVar 'mac) 'tg (EConst (Nil))) ctx))
    (not (Error? ret)))))

(define equal_invariant24
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant25
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant26
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant27
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define valid_invariant1
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx1 addr1))
    (match-define (cons ret _) (Eval (ECVar (EVar 'cpa) 'h (EConst (Nil))) ctx))
    (not (Error? ret)))))

(define (equivalent4)
  (define ctx13 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs5 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ENew (list (Init 'e (EVar '_e) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))) #t)) (ESeq (EMethod 'enc (list (EVar 'a 'value) (EVar 'm 'value)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a 'value) (EVar 'c (list 'value 'value))) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define rhs5 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ENew (list (Init 'e (EVar '_e) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECVar (EVar 'cpa) 'h (EVar 'em)))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define invariants (list invariant0 equal_invariant20 equal_invariant21 equal_invariant22 equal_invariant23 valid_invariant0 equal_invariant24 equal_invariant25 equal_invariant26 equal_invariant27 valid_invariant1))
  (check-proof (Equivalent ctx13 lhs5 rhs5 invariants)))

(define equal_invariant28
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant29
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant30
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant31
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant32
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant33
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant34
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant35
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define valid_invariant2
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx1 addr1))
    (match-define (cons ret _) (Eval (ECVar (EVar 'cpa) 'h (EConst (Nil))) ctx))
    (not (Error? ret)))))

(define (equivalent5)
  (define ctx16 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs6 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ENew (list (Init 'e (EVar '_e) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECVar (EVar 'cpa) 'h (EVar 'em)))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define rhs6 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ENew (list (Init 'e (EVar '_e) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define invariants (list equal_invariant28 equal_invariant29 equal_invariant30 equal_invariant31 equal_invariant32 equal_invariant33 equal_invariant34 equal_invariant35 valid_invariant2))
  (check-proof (Equivalent ctx16 lhs6 rhs6 invariants)))

(define equal_invariant36
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant37
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant38
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant39
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant40
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant41
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant42
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant43
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant44
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent6)
  (define ctx19 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs7 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ENew (list (Init 'e (EVar '_e) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define rhs7 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaC (list (EVar '_e))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define invariants (list equal_invariant36 equal_invariant37 equal_invariant38 equal_invariant39 equal_invariant40 equal_invariant41 equal_invariant42 equal_invariant43 equal_invariant44))
  (check-proof (Equivalent ctx19 lhs7 rhs7 invariants)))

(define equal_invariant45
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant46
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant47
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant48
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant49
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant50
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant51
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant52
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'h (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent7)
  (define ctx22 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs8 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaC (list (EVar '_e))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define rhs8 (ENew (list (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaC (list (EVar '_e))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define invariants (list equal_invariant45 equal_invariant46 equal_invariant47 equal_invariant48 equal_invariant49 equal_invariant50 equal_invariant51 equal_invariant52))
  (check-proof (Equivalent ctx22 lhs8 rhs8 invariants)))

(define (validrewrite1)
  (define ctx25 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs9 (ENew (list (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaC (list (EVar '_e))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define rhs9 (ENew (list (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define assumptions1 (list(cons (EVar '_e) (ECall (EConst (Nil)) 'Enc (list (EVar '_e)))) (cons (ECall (EConst (Nil)) 'CpaC (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaI (list (EVar '_e)))) (cons (EVar '_mac) (ECall (EConst (Nil)) 'MacI (list (EVar '_mac)))) (cons (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) (EVar '_e)) (cons (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaC (list (EVar '_e)))) (cons (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) (EVar '_mac))))
  (check-proof (ValidRewrite lhs9 rhs9 ctx25 (ECall (EConst (Nil)) 'CpaC (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) assumptions1)))

(define equal_invariant53
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant54
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant55
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant56
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant57
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant58
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent8)
  (define ctx26 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs10 (ENew (list (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define rhs10 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define invariants (list equal_invariant53 equal_invariant54 equal_invariant55 equal_invariant56 equal_invariant57 equal_invariant58))
  (check-proof (Equivalent ctx26 lhs10 rhs10 invariants)))

(define equal_invariant59
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant60
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant61
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant62
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define valid_invariant3
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx2 addr2))
    (match-define (cons ret _) (Eval (EVar 'e) ctx))
    (not (Error? ret)))))

(define equal_invariant63
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant64
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant65
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant66
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent9)
  (define ctx29 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs11 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'cpa) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'cpa) 'dec (list (EVar 'em)))))))))))
  (define rhs11 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECVar (EVar 'cpa) 'd (EVar 'em))))))))))
  (define invariants (list equal_invariant59 equal_invariant60 equal_invariant61 equal_invariant62 valid_invariant3 equal_invariant63 equal_invariant64 equal_invariant65 equal_invariant66))
  (check-proof (Equivalent ctx29 lhs11 rhs11 invariants)))

(define equal_invariant67
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant68
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant69
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant70
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define valid_invariant4
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx1 addr1))
    (match-define (cons ret _) (Eval (ECVar (EVar 'cpa) 'd (EConst (Nil))) ctx))
    (not (Error? ret)))))

(define equal_invariant71
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant72
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant73
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent10)
  (define ctx32 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs12 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECVar (EVar 'cpa) 'd (EVar 'em))))))))))
  (define rhs12 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar 'e))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECVar (EVar 'cpa) 'd (EVar 'em))))))))))
  (define invariants (list equal_invariant67 equal_invariant68 equal_invariant69 equal_invariant70 valid_invariant4 equal_invariant71 equal_invariant72 equal_invariant73))
  (check-proof (Equivalent ctx32 lhs12 rhs12 invariants)))

(define (validrewrite2)
  (define ctx35 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs13 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar 'e))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECVar (EVar 'cpa) 'd (EVar 'em))))))))))
  (define rhs13 (ENew (list (Init 'e (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar 'e))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a 'value) (EVar 'm 'value)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a 'value) (EVar 'c (list 'value 'value))) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECVar (EVar 'cpa) 'd (EVar 'em))))))))))
  (define assumptions2 (list(cons (EVar '_e) (ECall (EConst (Nil)) 'Enc (list (EVar '_e)))) (cons (ECall (EConst (Nil)) 'CpaC (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaI (list (EVar '_e)))) (cons (EVar '_mac) (ECall (EConst (Nil)) 'MacI (list (EVar '_mac)))) (cons (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) (EVar '_e)) (cons (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaC (list (EVar '_e)))) (cons (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) (EVar '_mac))))
  (check-proof (ValidRewrite lhs13 rhs13 ctx35 (EVar '_e) (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) assumptions2)))

(define args1 (list (EVar 'a 'value) (EVar 'em 'value) (EVar 't 'value)))
(define scope1 (for/list ([v args1]) (cons (EVar-name v) (HavocArg v))))

(define invariant1
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define body (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EVar 'mac) 'tg (ETuple (list (EVar 'a) (EVar 'em)))) (EVar 't))))) (ECVar (EVar 'cpa) 'd (EVar 'em)))))) (ECall (EConst (Nil)) '|| (list (ECall (EConst (Nil)) '! (list (ECVar (EVar 'mac) 'tg (ETuple (list (EVar 'a) (EVar 'em)))))) (ECall (EConst (Nil)) '& (list (ECVar (EVar 'cpa) 'd (EVar 'em)) (ECVar (EVar 'e) 'd (EVar 'em)))))))))
    (define qvs (symbolics scope1))
    (match-define (cons retL _) (Call_With_Scope body ctx1 scope1 addr1 (FUEL)))
    (match-define (cons retR _) (Call_With_Scope body ctx2 scope1 addr2 (FUEL)))
    (forall qvs (and (not (Error? retL)) (not (Error? retR)))))))

(define equal_invariant74
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant75
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'e (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'e (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant76
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'e (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (EVar '_e) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant77
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'e (EConst (Nil))) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'e (EConst (Nil))) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant78
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant79
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant80
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant81
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant82
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define valid_invariant5
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx1 addr1))
    (match-define (cons ret _) (Eval (ECVar (EVar 'cpa) 'd (EConst (Nil))) ctx))
    (not (Error? ret)))))

(define equal_invariant83
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define valid_invariant6
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx1 addr1))
    (match-define (cons ret _) (Eval (ECVar (EVar 'mac) 'tg (EConst (Nil))) ctx))
    (not (Error? ret)))))

(define equal_invariant84
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant85
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent11)
  (define ctx36 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs14 (ENew (list (Init 'e (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar 'e))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a 'value) (EVar 'm 'value)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a 'value) (EVar 'c (list 'value 'value))) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECVar (EVar 'cpa) 'd (EVar 'em))))))))))
  (define rhs14 (ENew (list (Init 'e (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar 'e))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a 'value) (EVar 'm 'value)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a 'value) (EVar 'c (list 'value 'value))) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECVar (EVar 'cpa) 'd (EVar 'em)))) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't))))))))))))))
  (define invariants (list invariant1 equal_invariant74 equal_invariant75 equal_invariant76 equal_invariant77 equal_invariant78 equal_invariant79 equal_invariant80 equal_invariant81 equal_invariant82 valid_invariant5 equal_invariant83 valid_invariant6 equal_invariant84 equal_invariant85))
  (check-proof (Equivalent ctx36 lhs14 rhs14 invariants)))

(define args2 (list (EVar 'a 'value) (EVar 'em 'value) (EVar 't 'value)))
(define scope2 (for/list ([v args2]) (cons (EVar-name v) (HavocArg v))))

(define invariant2
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define body (ECall (EConst (Nil)) '|| (list (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '== (list (EVar 't) (ECVar (EVar 'mac) 'tg (ETuple (list (EVar 'a) (EVar 'em)))))) (ECall (EConst (Nil)) '== (list (ECVar (EVar 'cpa) 'd (EVar 'em)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))))))))) (ECVar (EVar 'e) 'd (EVar 'em)))))))
    (define qvs (symbolics scope2))
    (match-define (cons retL _) (Call_With_Scope body ctx1 scope2 addr1 (FUEL)))
    (match-define (cons retR _) (Call_With_Scope body ctx2 scope2 addr2 (FUEL)))
    (forall qvs (and (not (Error? retL)) (not (Error? retR)))))))

(define equal_invariant86
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant87
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'e (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'e (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant88
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'e (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (EVar '_e) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant89
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'e (EConst (Nil))) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'e (EConst (Nil))) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant90
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant91
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant92
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant93
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant94
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'cpa (EConst (Nil))) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'cpa (EConst (Nil))) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define valid_invariant7
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx1 addr1))
    (match-define (cons ret _) (Eval (ECVar (EVar 'cpa) 'd (EConst (Nil))) ctx))
    (not (Error? ret)))))

(define equal_invariant95
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define valid_invariant8
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx1 addr1))
    (match-define (cons ret _) (Eval (ECVar (EVar 'mac) 'tg (EConst (Nil))) ctx))
    (not (Error? ret)))))

(define equal_invariant96
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant97
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent12)
  (define ctx39 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs15 (ENew (list (Init 'e (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar 'e))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a 'value) (EVar 'm 'value)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a 'value) (EVar 'c (list 'value 'value))) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECVar (EVar 'cpa) 'd (EVar 'em)))) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't))))))))))))))
  (define rhs15 (ENew (list (Init 'e (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar 'e))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))
  (define invariants (list invariant2 equal_invariant86 equal_invariant87 equal_invariant88 equal_invariant89 equal_invariant90 equal_invariant91 equal_invariant92 equal_invariant93 equal_invariant94 valid_invariant7 equal_invariant95 valid_invariant8 equal_invariant96 equal_invariant97))
  (check-proof (Equivalent ctx39 lhs15 rhs15 invariants)))

(define (validrewrite3)
  (define ctx42 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs16 (ENew (list (Init 'e (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar 'e))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))
  (define rhs16 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar 'e))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))
  (define assumptions3 (list(cons (EVar '_e) (ECall (EConst (Nil)) 'Enc (list (EVar '_e)))) (cons (ECall (EConst (Nil)) 'CpaC (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaI (list (EVar '_e)))) (cons (EVar '_mac) (ECall (EConst (Nil)) 'MacI (list (EVar '_mac)))) (cons (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) (EVar '_e)) (cons (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaC (list (EVar '_e)))) (cons (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) (EVar '_mac))))
  (check-proof (ValidRewrite lhs16 rhs16 ctx42 (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) (EVar '_e) assumptions3)))

(define valid_invariant9
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define ctx (Context-with-ths ctx1 addr1))
    (match-define (cons ret _) (Eval (ECVar (EVar 'cpa) 'd (EConst (Nil))) ctx))
    (not (Error? ret)))))

(define equal_invariant98
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant99
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant100
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant101
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'tg (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant102
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'mac (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent13)
  (define ctx43 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs17 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'cpa (ECall (EConst (Nil)) 'CpaI (list (EVar 'e))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EAssign (ECVar (EVar 'cpa) 'd (EVar 'em)) (EVar 'm)))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))
  (define rhs17 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EVar 'em))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))
  (define invariants (list valid_invariant9 equal_invariant98 equal_invariant99 equal_invariant100 equal_invariant101 equal_invariant102))
  (check-proof (Equivalent ctx43 lhs17 rhs17 invariants)))

(define (validrewrite4)
  (define ctx46 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs18 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EVar 'em))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))
  (define rhs18 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (EVar '_mac) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EVar 'em))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))
  (define assumptions4 (list(cons (EVar '_e) (ECall (EConst (Nil)) 'Enc (list (EVar '_e)))) (cons (ECall (EConst (Nil)) 'CpaC (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaI (list (EVar '_e)))) (cons (EVar '_mac) (ECall (EConst (Nil)) 'MacI (list (EVar '_mac)))) (cons (ECall (EConst (Nil)) 'Enc (list (EVar '_e))) (EVar '_e)) (cons (ECall (EConst (Nil)) 'CpaI (list (EVar '_e))) (ECall (EConst (Nil)) 'CpaC (list (EVar '_e)))) (cons (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) (EVar '_mac))))
  (check-proof (ValidRewrite lhs18 rhs18 ctx46 (ECall (EConst (Nil)) 'MacI (list (EVar '_mac))) (EVar '_mac) assumptions4)))

(define equal_invariant103
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'e (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant104
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'e (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant105
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent14)
  (define ctx47 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs19 (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (EVar '_mac) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))))) (EVar 'em))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (ETuple (list (EVar 'em) (EVar 't)))))) (EVar 'm)))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))
  (define rhs19 (ENew (list (Init 'e (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (EVar '_mac) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EVar 'em))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))
  (define invariants (list equal_invariant103 equal_invariant104 equal_invariant105))
  (check-proof (Equivalent ctx47 lhs19 rhs19 invariants)))

(define equal_invariant106
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant107
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (EVar '_lhs) 'd (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (EVar '_rhs) 'd (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant108
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'e (EConst (Nil))) 'e (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'e (EConst (Nil))) 'e (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define equal_invariant109
  (EquivalenceInvariant (lambda (ctx1 ctx2 addr1 addr2)
    (define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))
    (define ctx1* (extend-with '_lhs (Ref addr1) ctx1))
    (define ctx2* (extend-with '_rhs (Ref addr2) ctx2))
    (match-define (cons lhs* _) (Eval (ECVar (ECVar (EVar '_lhs) 'e (EConst (Nil))) 'mac (EConst (Nil))) ctx1*))
    (match-define (cons rhs* _) (Eval (ECVar (ECVar (EVar '_rhs) 'e (EConst (Nil))) 'mac (EConst (Nil))) ctx2*))
    (equal? lhs* rhs*))))

(define (equivalent15)
  (define ctx50 (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (ESeq (EMethod 'MacI (list (EVar 'mac)) (ENew (list (Init 'mac (EConst (Nil)) #t) (Init 'tg (EConst (Int 0)) #f)) (ESeq (EMethod 'tag (list (EVar 'm)) (EAssign (ECVar (EConst (Nil)) 'tg (EVar 'm)) (ECall (EVar 'mac) 'tag (list (EVar 'm))))) (EMethod 'verify (list (EVar 'm) (EVar 't)) (ECall (EConst (Nil)) '& (list (EVar 't) (ECall (EConst (Nil)) '== (list (ECVar (EConst (Nil)) 'tg (EVar 'm)) (EVar 't))))))))) (EMethod 'Enc (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (ECall (EConst (Nil)) '! (list (ECVar (EConst (Nil)) 'd (EVar 'c)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))) (EMethod 'CpaC (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'h (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'm)))) (EAssign (ECVar (EConst (Nil)) 'h (EVar 'c)) (EConst (Int 1))))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECall (EConst (Nil)) '& (list (ECVar (EConst (Nil)) 'h (EVar 'c)) (ECall (EVar 'e) 'dec (list (EVar 'c)))))))))) (EMethod 'CpaI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (EVar 'c)) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'c)) (ECVar (EConst (Nil)) 'd (EVar 'c))))))) (EMethod 'AeadI (list (EVar 'e)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))) (EMethod 'EtM (list (EVar 'e) (EVar 'mac)) (ENew (list (Init 'e (EConst (Nil)) #t) (Init 'mac (EConst (Nil)) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'c) (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))))) (EMethod 'zero (list (EVar 'm)) (ECall (EConst (Nil)) '& (list (EVar 'm) (EConst (Int 0)))))) (EAssign (EVar '_e) (ECall (EConst (Nil)) 'adversary (list )))) (EAssign (EVar '_mac) (ECall (EConst (Nil)) 'adversary (list )))))
  (define lhs20 (ENew (list (Init 'e (ENew (list (Init 'e (EVar '_e) #t) (Init 'mac (EVar '_mac) #t)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EVar 'm) (EAssign (EVar 'em) (ECall (EVar 'e) 'enc (list (EVar 'm)))))) (EVar 'em))) (EAssign (EVar 't) (ECall (EVar 'mac) 'tag (list (ETuple (list (EVar 'a) (EVar 'em)))))))) (ETuple (list (EVar 'em) (EVar 't)))))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ESeq (EAssign (EVar 'em) (ECVar (EVar 'c) 'get (EConst (Int 0)))) (ESeq (EAssign (EVar 't) (ECVar (EVar 'c) 'get (EConst (Int 1)))) (ECall (EConst (Nil)) '& (list (ECall (EVar 'mac) 'verify (list (ETuple (list (EVar 'a) (EVar 'em))) (EVar 't))) (ECall (EVar 'e) 'dec (list (EVar 'em)))))))))) #t) (Init 'd (EConst (Int 0)) #f)) (ESeq (EMethod 'enc (list (EVar 'a) (EVar 'm)) (ECall (EConst (Nil)) '& (list (ECall (EConst (Nil)) '& (list (EAssign (EVar 'c) (ECall (EVar 'e) 'enc (list (EVar 'a) (ECall (EConst (Nil)) 'zero (list (EVar 'm)))))) (EAssign (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c)))) (EVar 'm)))) (EVar 'c)))) (EMethod 'dec (list (EVar 'a) (EVar 'c)) (ECVar (EConst (Nil)) 'd (ETuple (list (EVar 'a) (EVar 'c))))))))
  (define rhs20 (ECall (EConst (Nil)) 'AeadI (list (ECall (EConst (Nil)) 'EtM (list (EVar '_e) (EVar '_mac))))))
  (define invariants (list equal_invariant106 equal_invariant107 equal_invariant108 equal_invariant109))
  (check-proof (Equivalent ctx50 lhs20 rhs20 invariants)))

(equivalent0)

(validrewrite0)

(equivalent1)

(equivalent2)

(equivalent3)

(equivalent4)

(equivalent5)

(equivalent6)

(equivalent7)

(validrewrite1)

(equivalent8)

(equivalent9)

(equivalent10)

(validrewrite2)

(equivalent11)

(equivalent12)

(validrewrite3)

(equivalent13)

(validrewrite4)

(equivalent14)

(equivalent15)
