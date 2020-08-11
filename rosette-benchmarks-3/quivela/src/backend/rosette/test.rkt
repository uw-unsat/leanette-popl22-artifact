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

(require rackunit
         "eval.rkt")


(define (TestContext n v)
  (Context '() (list (cons 0 (Object (list (cons n v))))) (list (cons 0 '())) 0 1))
(define (TestContext_Object1 obj)
  (match-define (Context scope objs methods ths nextAddr) (EmptyContext))
  (Context scope (cons (cons 1 obj) objs) (cons (cons 1 '()) methods) ths (add1 nextAddr)))
(define (TestObject n v)
  (Object (list (cons n v))))

(define (Eval_Ret e ctx)
  (match-define (cons ret ctx2) (Eval e ctx))
  ret)

; 5
(check-equal?
 (Eval_EmptyContext (EConst (Int 5)))
 (Int 5))

; x
(check-equal?
 (Eval_Ret (EVar 'x) (TestContext 'x (Int 5)))
 (Int 5))

; 5; 6
(check-equal?
 (Eval_EmptyContext (ESeq (EConst (Int 5)) (EConst (Int 6))))
 (Int 6))

; x[1]
(check-equal?
 (Eval_Ret (ECVar (EConst (Nil)) 'x (EConst (Int 1)))
           (TestContext 'x (Map (list (cons (Int 1) (Int 2))))))
 (Int 2))

; 1.x
(check-equal?
 (Eval_Ret (ECVar (EConst (Ref 1)) 'x (EConst (Nil)))
           (TestContext_Object1 (Object (list (cons 'x (Int 5))))))
 (Int 5))

; 1.x[2]
(check-equal?
 (Eval_Ret (ECVar (EConst (Ref 1)) 'x (EConst (Int 2)))
           (TestContext_Object1 (Object (list (cons 'x (Map (list (cons (Int 2) (Int 5)))))))))
 (Int 5))

; x = 5
(check-equal?
 (Eval_EmptyContext (ESeq (EAssign (EVar 'x) (EConst (Int 5))) (EVar 'x)))
 (Int 5))

; x = y
(check-equal?
 (Eval_Ret (ESeq (EAssign (EVar 'x) (EVar 'y)) (EVar 'x))
           (TestContext 'y (Int 5)))
 (Int 5))

; x[1] = 5
(define Test_Assign_CVar_Idx
  (ESeq (EAssign (ECVar (EConst (Nil)) 'x (EConst (Int 1))) (EConst (Int 5)))
        (ECVar (EConst (Nil)) 'x (EConst (Int 1)))))
; ... where x is not previously allocated
(check-pred
 Error?
 (Eval_EmptyContext Test_Assign_CVar_Idx))
; ... where x is previously a nat
(check-equal?
 (Eval_Ret Test_Assign_CVar_Idx (TestContext 'x (Int 0)))
 (Int 5))
; ... where x is already a map
(check-equal?
 (Eval_Ret Test_Assign_CVar_Idx (TestContext 'x (Map (list (cons (Int 2) (Int 3))))))
 (Int 5))

; 1.x = 5
(define Test_Assign_CVar_Obj
  (ESeq (EAssign (ECVar (EConst (Ref 1)) 'x (EConst (Nil))) (EConst (Int 5)))
        (ECVar (EConst (Ref 1)) 'x (EConst (Nil)))))
; ... where 1 is not a valid ref
(check-pred
 Error?
 (Eval_EmptyContext Test_Assign_CVar_Obj))
; ... where 1 is a valid ref, x is not previously set
(check-equal?
 (Eval_Ret Test_Assign_CVar_Obj (TestContext_Object1 (Object '())))
 (Int 5))
; ... where 1 is a valid ref, x is previously set
(check-equal?
 (Eval_Ret Test_Assign_CVar_Obj (TestContext_Object1 (Object (list (cons 'x (Int 2))))))
 (Int 5))

; 1.x[2] = 5
(define Test_Assign_CVar_Obj_Idx
  (ESeq (EAssign (ECVar (EConst (Ref 1)) 'x (EConst (Int 2))) (EConst (Int 5)))
        (ECVar (EConst (Ref 1)) 'x (EConst (Int 2)))))
; ... where 1 is not a valid ref
(check-pred
 Error?
 (Eval_EmptyContext Test_Assign_CVar_Obj_Idx))
; ... where 1 is a valid ref, x is not previously set
(check-equal?
 (Eval_Ret Test_Assign_CVar_Obj_Idx (TestContext_Object1 (Object '())))
 (Int 5))
; ... where 1 is a valid ref, x is previously a nat
(check-equal?
 (Eval_Ret Test_Assign_CVar_Obj_Idx (TestContext_Object1 (Object (list (cons 'x (Int 6))))))
 (Int 5))
; ... where 1 is a valid ref, x is previously a map
(check-equal?
 (Eval_Ret Test_Assign_CVar_Obj_Idx (TestContext_Object1 (Object (list (cons 'x (Map (list (cons (Int 2) (Int 3)))))))))
 (Int 5))

; new() {}
(let ()
  (match-define (cons ret ctx) (Eval (ENew '() (EConst (Nil))) (EmptyContext)))
  (check-pred Ref? ret)
  (check-equal? (length (Context-objs ctx)) 2)
  (check-equal? (length (Object-locals (assoc-get (Ref-addr ret) (Context-objs ctx)))) 0))

; new(a=5) {}
(let ()
  (match-define (cons ret ctx) (Eval (ENew (list (Init 'a (EConst (Int 5)))) (EConst (Nil))) (EmptyContext)))
  (check-pred Ref? ret)
  (check-equal? (length (Context-objs ctx)) 2)
  (check-equal? (length (Object-locals (assoc-get (Ref-addr ret) (Context-objs ctx)))) 1)
  (check-equal? (assoc-get 'a (Object-locals (assoc-get (Ref-addr ret) (Context-objs ctx)))) (Int 5)))

; new() { get(b) { b } }
(let ()
  (match-define (cons ret ctx) (Eval (ENew '() (EMethod 'get '(b) (EVar 'b))) (EmptyContext)))
  (check-pred Ref? ret)
  (check-equal? (length (Context-objs ctx)) 2)
  (check-equal? (length (assoc-get (Ref-addr ret) (Context-methods ctx))) 1)
  (check-equal? (assoc-get 'get (assoc-get (Ref-addr ret) (Context-methods ctx)))
                (Method 'get '(b) (EVar 'b))))

; x = new() { get(b) { b } }; x.get(5)
(check-equal?
 (Eval_EmptyContext (ESeq (EAssign (EVar 'x) (ENew '() (EMethod 'get '(b) (EVar 'b)))) (ECall (EVar 'x) 'get (list (EConst (Int 5))))))
 (Int 5))
                    
; x = new() { get(b) { b } }; x.get()
(check-pred
 Error?
 (Eval_EmptyContext (ESeq (EAssign (EVar 'x) (ENew '() (EMethod 'get '(b) (EVar 'b)))) (ECall (EVar 'x) 'get (list)))))

; x = new() { get(b) { b } }; x.foo()
(check-pred
 Error?
 (Eval_EmptyContext (ESeq (EAssign (EVar 'x) (ENew '() (EMethod 'get '(b) (EVar 'b)))) (ECall (EVar 'x) 'foo (list)))))

; x = 5; x.foo(5)
(check-pred
 Error?
 (Eval_EmptyContext (ESeq (EAssign (EVar 'x) (EConst (Int 5))) (ECall (EVar 'x) 'foo (list)))))

; 5 + 6
(check-equal?
 (Eval_EmptyContext (ECall (EConst (Nil)) '+ (list (EConst (Int 5)) (EConst (Int 6)))))
 (Int 11))

; ite x 1 2
(define Test_ITE (EITE (EVar 'x) (EConst (Int 2)) (EConst (Int 3))))
; ... where x is undefined
(check-pred
 Error?
 (Eval_EmptyContext Test_ITE))
; ... where x is truthy
(check-equal?
 (Eval_Ret Test_ITE (TestContext 'x (Int 1)))
 (Int 2))
; ... where x is falsy
(check-equal?
 (Eval_Ret Test_ITE (TestContext 'x (Int 0)))
 (Int 3))

; if x { y := 5 } else { y := 6 }; y
(define Test_ITE_CTX (ESeq (EITE (EVar 'x) (EAssign (EVar 'y) (EConst (Int 5))) (EAssign (EVar 'y) (EConst (Int 6))))
                           (EVar 'y)))
; ... where x is truthy
(check-equal?
 (Eval_Ret Test_ITE_CTX (TestContext 'x (Int 1)))
 (Int 5))
; ... where x is falsy
(check-equal?
 (Eval_Ret Test_ITE_CTX (TestContext 'x (Int 0)))
 (Int 6))

; if (y = x) { 5 } else { 6 }; y     // note that's 'assign x to y', not a comparison
(define Test_ITE_Cond_CTX (ESeq (EITE (EAssign (EVar 'y) (EVar 'x)) (EConst (Int 5)) (EConst (Int 6)))
                                (EVar 'y)))
; ... where x is truthy
(check-equal?
 (Eval_Ret Test_ITE_Cond_CTX (TestContext 'x (Int 1)))
 (Int 1))
; ... where x is falsy
(check-equal?
 (Eval_Ret Test_ITE_Cond_CTX (TestContext 'x (Int 0)))
 (Int 0))

#|
    // ite x 1 2
    var Test_ITE := EITE(EVar("x"), EConst(Int(2)), EConst(Int(3)));
    // ... where x is undefined
    assert Eval_EmptyContext(Test_ITE) == Error();
    // ... where x is truthy
    assert Eval(Test_ITE, TestContext("x", Int(1)), FUEL).0 == Int(2);
    // ... where x is falsy
    assert Eval(Test_ITE, TestContext("x", Int(0)), FUEL).0 == Int(3);

    // if x { y := 5 } else { y := 6 }; y
    var Test_ITE_Ctx := ESeq(EITE(EVar("x"), EAssign(EVar("y"), EConst(Int(5))), EAssign(EVar("y"), EConst(Int(6)))),
                                  EVar("y"));
    // ... where x is truthy
    assert Eval(Test_ITE_Ctx, TestContext("x", Int(1)), FUEL).0 == Int(5);
    // ... where x is falsy
    assert Eval(Test_ITE_Ctx, TestContext("x", Int(0)), FUEL).0 == Int(6);

    // if (y = x) { 5 } else { 6 }; y     // note that's 'assign x to y', not a comparison
    var Test_ITE_Cond_Ctx := ESeq(EITE(EAssign(EVar("y"), EVar("x")), EConst(Int(5)), EConst(Int(6))),
                                  EVar("y"));
    // ... where y is truthy
    assert Eval(Test_ITE_Cond_Ctx, TestContext("x", Int(1)), FUEL).0 == Int(1);
    // ... where y is falsy
    assert Eval(Test_ITE_Cond_Ctx, TestContext("x", Int(0)), FUEL).0 == Int(0);
|#