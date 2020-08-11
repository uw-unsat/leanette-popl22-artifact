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

(require rosette/lib/match
         "lang.rkt" "print.rkt" "adversary.rkt")
(provide (all-defined-out)
         (all-from-out "lang.rkt"))

(define (ValidRef ref ctx)
  (and (assoc ref (Context-objs ctx))
       (assoc ref (Context-methods ctx))
       #t))


(define (InitLocals locals ctx fuel)
  (let loop ([locals locals][ctx ctx][acc '()][immut '()])
    (if (null? locals)
        (list ctx acc immut)
        (let ([l (car locals)])
          (define e (if (equal? (Init-val l) (EConst (Nil))) (EVar (Init-name l)) (Init-val l)))
          (match-let* ([old-scope (Context-scope ctx)]
                       [ctx* (Context-with-scope ctx (append acc old-scope))]
                       [(cons ret ctx1*) (Eval e ctx* fuel)]
                       [ctx1 (Context-with-scope ctx1* old-scope)])
            (loop (cdr locals)
                  ctx1 
                  (cons (cons (Init-name l) ret) acc) 
                  (if (Init-immutable? l) (cons (Init-name l) immut) immut)))))))

(define (EvalArgs names exprs ctx fuel)
  (let loop ([names names][exprs exprs][ctx ctx][acc '()])
    (if (null? names)
        (cons acc ctx)
        (match-let ([(cons val ctx1) (Eval (car exprs) ctx fuel)])
          (loop (cdr names) (cdr exprs) ctx1 (cons (cons (EVar-name (car names)) val) acc))))))
(define (EvalArgs/list exprs ctx fuel)
  (let loop ([exprs exprs][ctx ctx][acc '()])
    (if (null? exprs)
        (cons (reverse acc) ctx)
        (match-let ([(cons val ctx1) (Eval (car exprs) ctx fuel)])
          (loop (cdr exprs) ctx1 (cons val acc))))))

(define (EvalTupleElts exprs ctx fuel)
  (let loop ([exprs exprs][ctx ctx][acc '()])
    (if (null? exprs)
        (cons (reverse acc) ctx)
        (match-let ([(cons val ctx1) (Eval (car exprs) ctx fuel)])
          (let ([acc* (cons val acc) #;(if (Tuple? val) (append (reverse (Tuple-elts val)) acc) (cons val acc))])
            (loop (cdr exprs) ctx1 acc*))))))


(define (Call_With_Scope body ctx scope ths fuel)
  (define oldThs (Context-ths ctx))
  (define oldScope (Context-scope ctx))
  (match-define (cons ret ctx1) (Eval body (Context-with-scope+ths ctx scope ths) fuel))
  (cons ret (Context-with-scope+ths ctx1 oldScope oldThs)))


(define (Call_Builtin_Binop name args ctx fuel)
  (cond
    [(equal? name '&)
     (match-let ([(cons a ctx1) (Eval (car args) ctx fuel)])
       (cond
         [(Error? a) (cons a ctx1)]
         [else (Eval (cadr args) ctx1 fuel)]))]
    [(equal? name '||)
     (match-let ([(cons a ctx1) (Eval (car args) ctx fuel)])
       (cond
         [(not (Error? a)) (cons a ctx1)]
         [else (Eval (cadr args) ctx1 fuel)]))]
    [(equal? name '==)
     (match-define (cons a ctx1) (Eval (car args) ctx fuel))
     (match-define (cons b ctx2) (Eval (cadr args) ctx1 fuel))
     (cons (if (equal? a b) (Int 1) (Error "not equal" name)) ctx2)]  ; to be consistent with & and |
    [else
     (match-define (cons a ctx1) (Eval (car args) ctx fuel))
     (match-define (cons b ctx2) (Eval (cadr args) ctx1 fuel))
     (cond
       [(Error? a) (cons a ctx1)]
       [(Error? b) (cons b ctx2)]
       [(not (and (Int? a) (Int? b))) (cons (Error (format "arguments to ~v must be ints" name) #f) ctx2)]
       [else
        (define va (Int-val a))
        (define vb (Int-val b))
        (match name
          ['+ (cons (Int (+ va vb)) ctx2)]
          ['- (cons (Int (- va vb)) ctx2)]
          ['* (cons (Int (* va vb)) ctx2)]
          ['/ (if (equal? vb 0)
                  (cons (Error "divide by zero" name) ctx2)
                  (cons (Int (/ va vb)) ctx2))]
          ['< (cons (Int (if (< va vb) 1 0)) ctx2)]
          ['> (cons (Int (if (> va vb) 1 0)) ctx2)]
          [_ (cons (Error (format "unrecognized op ~v" name) name) ctx2)])])]))

(define (Call_Builtin_Unop name args ctx fuel)
  (match-define (cons a ctx1) (Eval (car args) ctx fuel))
  (cond
    [(equal? name '!) (cons (if (Error? a) (Int 1) (Error "negated" name)) ctx1)]
    [else (cons (Error (format "unrecognized op ~v" name) name) ctx1)]))

(define (Call_Builtin_0op name args ctx fuel)
  (cond
    [(equal? name 'adversary)
     (define addr (Context-nextAddr ctx))
     (define ctx1 (Context (Context-scope ctx)
                           (assoc-set addr (Object '()) (Context-objs ctx))
                           (assoc-set addr (adversary '()) (Context-methods ctx))
                           (Context-ths ctx)
                           (add1 addr)
                           (cons (cons addr '()) (Context-metadata ctx))))
     (cons (Ref addr) ctx1)]
    [else
     (cons (Error (format "unrecognized op ~v" name) name) ctx)]))

(define (Call_Builtin name args ctx fuel)
  (define arity (Is_Builtin_Arity name))
  (cond
    [(not (equal? arity (length args)))
     (cons (Error (format "wrong number of args (got ~v, expected ~v)" (length args) arity) name) ctx)]
    [(equal? arity 2)
     (Call_Builtin_Binop name args ctx fuel)]
    [(equal? arity 1)
     (Call_Builtin_Unop name args ctx fuel)]
    [(equal? arity 0)
     (Call_Builtin_0op name args ctx fuel)]
    [else (cons (Error (format "unknown arity ~v" arity) name) ctx)]))


; Dealing with association lists
(define (assoc-get x xs)
  (define a (assoc x xs))
  (if a (cdr a) a))
(define (assoc-has? x xs)
  (for/all ([xs xs])
    (let loop ([xs xs])
      (cond [(null? xs) #f]
            [(equal? x (caar xs)) #t]
            [else (loop (cdr xs))]))))
(define (assoc-set x v xs)
  (let loop ([xs xs])
    (cond [(null? xs) (list (cons x v))]
          [(equal? (caar xs) x) (cons (cons x v) (cdr xs))]
          [else (cons (car xs) (loop (cdr xs)))])))

(define (Eval_Var e ctx fuel)
  (define n (EVar-name e))
  (if (assoc-has? n (Context-scope ctx))
      (cons (assoc-get n (Context-scope ctx)) ctx)
      (if (and (ValidRef (Context-ths ctx) ctx)
               (assoc-get n (Object-locals (assoc-get (Context-ths ctx) (Context-objs ctx)))))
          (cons (assoc-get n (Object-locals (assoc-get (Context-ths ctx) (Context-objs ctx)))) ctx)
          (if (and (ValidRef 0 ctx)
                   (assoc-get n (Object-locals (assoc-get 0 (Context-objs ctx)))))
              (cons (assoc-get n (Object-locals (assoc-get 0 (Context-objs ctx)))) ctx)
              (cons (Error "undefined variable" e) ctx)))))

(define (Eval_Tuple e ctx fuel)
  (match-define (cons elts ctx1) (EvalTupleElts (ETuple-vals e) ctx fuel))
  (cons (Tuple elts) ctx1))

(define (Eval_Seq e ctx fuel)
  (match-define (ESeq e1 e2) e)
  (match-define (cons v1 ctx1) (Eval e1 ctx fuel))
  (Eval e2 ctx1 fuel))

(define (Eval_CVar e ctx fuel)
  (match-define (ECVar obj name idx) e)
  (match-define (cons vobj ctx1) (Eval obj ctx fuel))
  (for/all ([vobj vobj])
    (if (not (or (Ref? vobj) (Nil? vobj) (Tuple? vobj)))
        (cons (Error "invalid base object for CVar" e) ctx1)
        (let ()
          (if (Tuple? vobj)
              (let ()
                (match-define (cons vidx ctx2) (Eval idx ctx1 fuel))
                (if (and (Int? vidx) (<= 0 (Int-val vidx)) (< (Int-val vidx) (length (Tuple-elts vobj))))
                    (cons (list-ref (Tuple-elts vobj) (Int-val vidx)) ctx2)
                    (cons (Error (format "tuple index ~v out of range (got ~v elts)" (Int-val idx) (length (Tuple-elts vobj))) e) ctx2)))
              (let ()
                (define base
                  (cond [(Ref? vobj)
                         (if (ValidRef (Ref-addr vobj) ctx1)
                             (Object-locals (assoc-get (Ref-addr vobj) (Context-objs ctx1)))
                             '())]
                        [(assoc-get name (Context-scope ctx1))
                         (Context-scope ctx1)]
                        [(and (ValidRef (Context-ths ctx1) ctx1)
                              (assoc-get name (Object-locals (assoc-get (Context-ths ctx1) (Context-objs ctx1)))))
                         (Object-locals (assoc-get (Context-ths ctx1) (Context-objs ctx1)))]
                        [(and (ValidRef 0 ctx1)
                              (assoc-get name (Object-locals (assoc-get 0 (Context-objs ctx1)))))
                         (Object-locals (assoc-get 0 (Context-objs ctx1)))]
                        [else '()]))
                (if (assoc-get name base)
                    (let ()
                      (define ret (assoc-get name base))
                      (match-define (cons vidx ctx2) (Eval idx ctx1 fuel))
                      (cond [(Nil? vidx) (cons ret ctx2)]
                            [(and (Map? ret) (assoc-get vidx (Map-vals ret)))
                             (cons (assoc-get vidx (Map-vals ret)) ctx2)]
                            [else (cons (Error "invalid idx" e) ctx2)]))  ; idx is specified, var is not yet a map -- return default value
                    (cons (Error "undefined variable" e) ctx1))))))))

(define (Eval_New e ctx fuel)
  (match-define (ENew locals body) e)
  (match-define (list ctx1 elocals immut) (InitLocals locals ctx fuel))
  (define oldThs (Context-ths ctx1))
  (define oldScope (Context-scope ctx1))
  (define addr (Context-nextAddr ctx1))
  (define ctx2 (Context oldScope
                        (assoc-set addr (Object elocals) (Context-objs ctx1))
                        (assoc-set addr '() (Context-methods ctx1))
                        addr
                        (add1 addr)
                        (cons (cons addr immut) (Context-metadata ctx1))))
  (match-define (cons ret ctx3) (Eval body ctx2 fuel))
  (cons (Ref addr) (Context-with-scope+ths ctx3 oldScope oldThs)))

(define (Eval_Method e ctx fuel)
  (if (ValidRef (Context-ths ctx) ctx)
      (let ([mtd (Method (EMethod-name e) (EMethod-args e) (EMethod-body e))])
        (define old-methods (assoc-get (Context-ths ctx) (Context-methods ctx)))
        (define new-methods (assoc-set (EMethod-name e) mtd old-methods))
        (cons (Nil) (Context-with-methods ctx (assoc-set (Context-ths ctx) new-methods (Context-methods ctx)))))
      (cons (Error "no valid `this` reference" e) ctx)))

(define (Eval_Assign e ctx fuel)
  (match-define (EAssign lhs rhs) e)
  (match-define (cons erhs ctx1) (Eval rhs ctx fuel))
  (cond
    ; plain Var on the LHS; just set it in the right scope
    [(EVar? lhs)
     (define n (EVar-name lhs))
     (cond
       [(assoc-get n (Context-scope ctx))  ; already a local
        (cons erhs (Context-with-scope ctx1 (assoc-set n erhs (Context-scope ctx1))))]
       [(and (ValidRef (Context-ths ctx1) ctx1)
             (assoc-get n (Object-locals (assoc-get (Context-ths ctx1) (Context-objs ctx1)))))  ; already a field
        (define old-obj (assoc-get (Context-ths ctx1) (Context-objs ctx1)))
        (define new-obj (Object (assoc-set n erhs (Object-locals old-obj))))
        (cons erhs (Context-with-objs ctx1 (assoc-set (Context-ths ctx1) new-obj (Context-objs ctx1))))]
       [(and (ValidRef 0 ctx1) (assoc-get n (Object-locals (assoc-get 0 (Context-objs ctx1)))))  ; already a global
        (define old-obj (assoc-get 0 (Context-objs ctx1)))
        (define new-obj (Object (assoc-set n erhs (Object-locals old-obj))))
        (cons erhs (Context-with-objs ctx1 (assoc-set 0 new-obj (Context-objs ctx1))))]
       [(and (ValidRef (Context-ths ctx1) ctx1) (not (equal? (Context-ths ctx1) 0)))  ; inside a method call, so restrict the scope of a new decl
        (cons erhs (Context-with-scope ctx1 (assoc-set n erhs (Context-scope ctx1))))]
       [(ValidRef 0 ctx1)  ; outside a method call, everything is a global
        (define old-obj (assoc-get 0 (Context-objs ctx1)))
        (define new-obj (Object (assoc-set n erhs (Object-locals old-obj))))
        (cons erhs (Context-with-objs ctx1 (assoc-set 0 new-obj (Context-objs ctx1))))]
       [else (cons (Error "cannot assign in this scope" e) ctx1)])]
    [(ECVar? lhs)
     (match-define (ECVar obj name idx) lhs)
     (match-define (cons eobj ctx2) (Eval obj ctx1 fuel))
     (match-define (cons eidx ctx3) (Eval idx ctx2 fuel))
     (for/all ([eobj eobj])
       (cond
         [(Error? eobj) (cons eobj ctx3)]
         [(Error? eidx) (cons eidx ctx3)]
         ; is the LHS a reference to an object?
         [(Ref? eobj)
          (if (not (ValidRef (Ref-addr eobj) ctx))
              (cons (Error "invalid base object for assignment" e) ctx3)
              (let ()
                (define orig (Object-locals (assoc-get (Ref-addr eobj) (Context-objs ctx3))))
                ; are we setting an index in a map?
                (if (Nil? eidx)
                    (let ()
                      (define new-obj (Object (assoc-set name erhs orig)))
                      (cons erhs (Context-with-objs ctx3 (assoc-set (Ref-addr eobj) new-obj (Context-objs ctx3)))))
                    (let ()
                      (define baseMap
                        (if (and (assoc-get name orig) (Map? (assoc-get name orig)))
                            (Map-vals (assoc-get name orig))
                            '()))
                      (define new-obj (Object (assoc-set name (Map (assoc-set eidx erhs baseMap)) orig)))
                      (cons erhs (Context-with-objs ctx3 (assoc-set (Ref-addr eobj) new-obj (Context-objs ctx3))))))))]
         [(Nil? eobj)  ; LHS is not a ref
          (cond
            [(Nil? eidx)
             (cond
               [(assoc-get name (Context-scope ctx))  ; already a local
                (cons erhs (Context-with-scope ctx3 (assoc-set name erhs (Context-scope ctx3))))]
               [(and (ValidRef (Context-ths ctx3) ctx3)
                     (assoc-get name (Object-locals (assoc-get (Context-ths ctx3) (Context-objs ctx3)))))  ; already a field
                (define old-obj (assoc-get (Context-ths ctx3) (Context-objs ctx3)))
                (define new-obj (Object (assoc-set name erhs (Object-locals old-obj))))
                (cons erhs (Context-with-objs ctx3 (assoc-set (Context-ths ctx3) new-obj (Context-objs ctx3))))]
               [(and (ValidRef 0 ctx3) (assoc-get name (Object-locals (assoc-get 0 (Context-objs ctx3)))))  ; already a global
                (define old-obj (assoc-get 0 (Context-objs ctx3)))
                (define new-obj (Object (assoc-set name erhs (Object-locals old-obj))))
                (cons erhs (Context-with-objs ctx3 (assoc-set 0 new-obj (Context-objs ctx3))))]
               [(ValidRef (Context-ths ctx3) ctx3)  ; inside a method call, so restrict the scope of a new decl
                (cons erhs (Context-with-scope ctx3 (assoc-set name erhs (Context-scope ctx3))))]
               [else (cons (Error "cannot assign in this scope" e) ctx3)])]
            [(assoc-get name (Context-scope ctx))  ; already a local
             (define old-val (assoc-get name (Context-scope ctx)))
             (define baseMap (if (Map? old-val) (Map-vals old-val) '()))
             (cons erhs (Context-with-scope ctx3 (assoc-set name (Map (assoc-set eidx erhs baseMap)) (Context-scope ctx3))))]
            [(and (ValidRef (Context-ths ctx3) ctx3)
                  (assoc-get name (Object-locals (assoc-get (Context-ths ctx) (Context-objs ctx3)))))  ; already a field
             (define old-obj (assoc-get (Context-ths ctx3) (Context-objs ctx3)))
             (define old-val (assoc-get name (Object-locals old-obj)))
             (define baseMap (if (Map? old-val) (Map-vals old-val) '()))
             (define newMap (Map (assoc-set eidx erhs baseMap)))
             (define new-obj (Object (assoc-set name newMap (Object-locals old-obj))))
             (cons erhs (Context-with-objs ctx3 (assoc-set (Context-ths ctx) new-obj (Context-objs ctx3))))]
            [(and (ValidRef 0 ctx3) (assoc-get name (Object-locals (assoc-get 0 (Context-objs ctx3)))))  ; already a global
             (define old-obj (assoc-get 0 (Context-objs ctx3)))
             (define old-val (assoc-get name (Object-locals old-obj)))
             (define baseMap (if (Map? old-val) (Map-vals old-val) '()))
             (define newMap (Map (assoc-set eidx erhs baseMap)))
             (define new-obj (Object (assoc-set name newMap (Object-locals old-obj))))
             (cons erhs (Context-with-objs ctx3 (assoc-set 0 new-obj (Context-objs ctx3))))]
            ; note: no default case; the variable must already exist to do a map assignment to it
            [else (cons (Error "cannot assign in this scope" e) ctx3)])]
         [else (cons (Error (format "invalid base object ~v for assignment" eobj) e) ctx3)]))]
    [else (cons (Error "invalid LHS for assignment" e) ctx1)]))

(define (Eval_Call e ctx fuel)
  (match-define (ECall obj name args) e)
  (match-define (cons eref ctx1) (Eval obj ctx fuel))
  (for/all ([eref eref])
  (cond
    [(Ref? eref)
     (cond
       [(not (ValidRef (Ref-addr eref) ctx1))
        (cons (Error "invalid base object for call" e) ctx1)]
       [(adversary? (assoc-get (Ref-addr eref) (Context-methods ctx1)))
        (define adv (assoc-get (Ref-addr eref) (Context-methods ctx1)))
        (match-define (cons eargs ctx2) (EvalArgs/list args ctx1 fuel))
        (cons (apply adv (cons name eargs)) ctx2)]
       [(not (assoc-get name (assoc-get (Ref-addr eref) (Context-methods ctx1))))
        (cons (Error (format "no method named ~v" name) e) ctx1)]
       [else
        (let ([mtd (assoc-get name (assoc-get (Ref-addr eref) (Context-methods ctx1)))])
          (if (not (equal? (length (Method-args mtd)) (length args)))
              (cons (Error (format "wrong number of args for ~v (got ~v, expected ~v)" name (length args) (length (Method-args mtd))) e) ctx1)
              (match-let ([(cons scope ctx2) (EvalArgs (Method-args mtd) args ctx1 fuel)])
                (Call_With_Scope (Method-body mtd) ctx2 scope (Ref-addr eref) fuel))))])]
    [(Nil? eref)
     (cond
       [(not (equal? (Is_Builtin_Arity name) -1))
        (Call_Builtin name args ctx1 fuel)]
       [else
        (define baseAddr
          (if (and (ValidRef (Context-ths ctx1) ctx1)
                   (assoc-get name (assoc-get (Context-ths ctx1) (Context-methods ctx1))))
              (Context-ths ctx1)
              0))
        (define mtd (assoc-get name (assoc-get baseAddr (Context-methods ctx1))))
        (if mtd
            (if (not (equal? (length (Method-args mtd)) (length args)))
                (cons (Error (format "wrong number of args for ~v (got ~v, expected ~v)" name (length args) (length (Method-args mtd))) e) ctx1)
                (match-let ([(cons scope ctx2) (EvalArgs (Method-args mtd) args ctx1 fuel)])
                  (Call_With_Scope (Method-body mtd) ctx2 scope (Context-ths ctx2) fuel)))
            (cons (Error (format "no method named ~v" name) e) ctx))])]
    [else (cons (Error "invalid base object for call" e) ctx)])))

(define (Eval_ITE e ctx fuel)
  (match-define (EITE con thn els) e)
  (match-define (cons econd ctx1) (Eval con ctx fuel))
  (cond
    [(or (Error? econd) (Nil? econd) (and (Int? econd) (equal? (Int-val econd) 0)))
     (Eval els ctx1 fuel)]
    [else (Eval thn ctx1 fuel)]))

(define (Eval e ctx [fuel 10])
  (if (= fuel 0)
      (let () (printf "\n\nOUT OF FUEL\n\n") (cons (Error "out of fuel" e) ctx))
      (let ([fuel1 (- fuel 1)])
        (match e
          [(EVar _) (Eval_Var e ctx fuel1)]
          [(EConst v) (cons v ctx)]
          [(ETuple _) (Eval_Tuple e ctx fuel1)]
          [(ESeq _ _) (Eval_Seq e ctx fuel1)]
          [(ECVar _ _ _) (Eval_CVar e ctx fuel1)]
          [(ENew _ _) (Eval_New e ctx fuel1)]
          [(EMethod _ _ _) (Eval_Method e ctx fuel1)]
          [(EAssign _ _) (Eval_Assign e ctx fuel1)]
          [(ECall _ _ _) (Eval_Call e ctx fuel1)]
          [(EITE _ _ _) (Eval_ITE e ctx fuel1)]
          [(ENop) (cons (Nil) ctx)]
          [_ (error 'Eval "unknown expression ~v" e)]))))


(define (EmptyContext)
  (Context '() (list (cons 0 (Object '()))) (list (cons 0 '())) 0 1 '()))

(define (Eval_EmptyContext e)
  (match-define (cons ret ctx) (Eval e (EmptyContext)))
  ret)
