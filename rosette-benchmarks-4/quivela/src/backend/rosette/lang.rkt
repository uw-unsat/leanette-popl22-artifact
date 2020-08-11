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

(provide (except-out (all-defined-out) EVar Init)
         (rename-out [EVar-ctor EVar] [Init-ctor Init]))

(define print-errors? (make-parameter #f))

; datatype Value = Int(val: int) | Tuple(elts: seq<Value>) | Map(vals: map<Value, Value>) | Ref(addr: Addr) | Nil() | Error()
(struct Value () #:transparent)
(struct Int Value (val) #:transparent)
(struct Tuple Value (elts) #:transparent)
(struct Map Value (vals) #:transparent)
(struct Ref Value (addr) #:transparent)
(struct Nil Value () #:transparent)
(struct Error Value (msg expr) #:transparent #:mutable
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (if (print-errors?)
         (write-string (format "<error: ~a @ ~a>" (Error-msg self) (Error-expr self)) port)
         (write-string "ε" port)))]
  #:methods gen:equal+hash
  [(define (equal-proc a b rec)
     (and (Error? a) (Error? b)))
   (define (hash-proc a rec)
     1024)
   (define (hash2-proc a rec)
     1025)])


; datatype Init = Init(name: Var, val: Expr)
(struct Init (name val immutable?) #:transparent
  #:methods gen:equal+hash
  [(define (equal-proc a b rec)
     (and (Init? a) (Init? b) (rec (Init-name a) (Init-name b)) (rec (Init-val a) (Init-val b))))
   (define (hash-proc a rec)
     (+ 2048 (rec (Init-name a)) (rec (Init-val a))))
   (define (hash2-proc a rec)
     (+ 2049 (rec (Init-name a)) (rec (Init-val a))))])
(define-match-expander Init-ctor
  (lambda (stx)
    (syntax-case stx ()
      [(_ name-pat val-pat) #'(Init name-pat val-pat _)]
      [(_ name-pat val-pat immut-pat) #'(Init name-pat val-pay immut-pat)]))
  (syntax-id-rules ()
    [(_ name val) (Init name val #f)]
    [(_ name val imm) (Init name val imm)]))

; datatype Expr = EVar(name: Var)
;               | EConst(val: Value)
;               | ESeq(e1: Expr, e2: Expr)
;               | ECVar(obj: Expr, name: Var, idx: Expr)  // compound var obj.name[idx]
;               | ENew(locals: seq<Init>, body: Expr)
;               | EMethod(name: Var, args: seq<Var>, body: Expr)
;               | EAssign(lhs: Expr, rhs: Expr)
;               | ECall(cobj: Expr, cname: Var, cargs: seq<Expr>)
;               | EITE(cond: Expr, thn: Expr, els: Expr)
;               | ENop()
(struct Expr () #:transparent)
(struct EVar Expr (name type) #:transparent
  #:methods gen:equal+hash
  [(define (equal-proc a b rec)
     (and (EVar? a) (EVar? b) (rec (EVar-name a) (EVar-name b))))
   (define (hash-proc a rec)
     (+ 4096 (rec (EVar-name a))))
   (define (hash2-proc a rec)
     (+ 4097 (rec (EVar-name a))))])
(struct EConst Expr (val) #:transparent)
(struct ETuple Expr (vals) #:transparent)
(struct ESeq Expr (e1 e2) #:transparent)
(struct ECVar Expr (obj name idx) #:transparent)
(struct ENew Expr (locals body) #:transparent)
(struct EMethod Expr (name args body) #:transparent)
(struct EAssign Expr (lhs rhs) #:transparent)
(struct ECall Expr (cobj cname cvars) #:transparent)
(struct EITE Expr (cond thn els) #:transparent)
(struct ENop Expr () #:transparent)

(define-match-expander EVar-ctor
  (lambda (stx)
    (syntax-case stx ()
      [(_ id-pat) #'(EVar id-pat _)]
      [(_ id-pat type-pat) #'(EVar id-pat type-pat)]))
  (syntax-id-rules ()
    [(_ id) (EVar id #f)]
    [(_ id type) (EVar id type)]))

; datatype Context = Context(scope: Env, objs: map<Addr, Object>, methods: map<Addr, map<Var, Method>>, ths: Addr, nextAddr: Addr)
(struct Context (scope objs methods ths nextAddr metadata) #:transparent)
(define (Context-with-scope ctx scope)
  (match-define (Context _ objs methods ths nextAddr meta) ctx)
  (Context scope objs methods ths nextAddr meta))
(define (Context-with-objs ctx objs)
  (match-define (Context scope _ methods ths nextAddr meta) ctx)
  (Context scope objs methods ths nextAddr meta))
(define (Context-with-methods ctx methods)
  (match-define (Context scope objs _ ths nextAddr meta) ctx)
  (Context scope objs methods ths nextAddr meta))
(define (Context-with-scope+ths ctx scope ths)
  (match-define (Context _ objs methods _ nextAddr meta) ctx)
  (Context scope objs methods ths nextAddr meta))
(define (Context-with-nextAddr ctx nextAddr)
  (match-define (Context scope objs methods ths _ meta) ctx)
  (Context scope objs methods ths nextAddr meta))
(define (Context-with-ths ctx ths)
  (match-define (Context scope objs methods _ nextAddr meta) ctx)
  (Context scope objs methods ths nextAddr meta))

; datatype Object = Object(locals: Env)
(struct Object (locals) #:transparent)

; datatype Method = Method(name: Var, args: seq<Var>, body: Expr)
(struct Method (name args body) #:transparent)


(define (Is_Builtin_Arity name)
  (cond
    [(member name '(+ - * / < > == & ||)) 2]
    [(member name '(!)) 1]
    [(member name '(adversary)) 0]
    [else -1]))