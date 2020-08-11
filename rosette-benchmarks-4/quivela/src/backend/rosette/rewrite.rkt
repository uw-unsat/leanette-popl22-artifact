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

(require "lang.rkt")
(provide rewrite-expr rewrite-context)

; return expr[e1 := e2]
(define (rewrite-expr expr e1 e2)
  (cond
    [(equal? expr e1) e2]
    [else
     (define rec (curryr rewrite-expr e1 e2))
     (match expr
       [(EVar _) expr]
       [(EConst _) expr]
       [(ETuple elts) (ETuple (map rec elts))]
       [(ESeq e1 e2) (ESeq (rec e1) (rec e2))]
       [(ECVar obj name idx) (ECVar (rec obj) name (rec idx))]
       [(ENew locals body)
        (ENew (for/list ([l locals]) (Init (Init-name l) (rec (Init-val l))))
              (rec body))]
       [(EMethod name args body)
        (EMethod name args (rec body))]
       [(EAssign lhs rhs)
        (EAssign (rec lhs) (rec rhs))]
       [(ECall obj name vars)
        (ECall (rec obj) name (map rec vars))]
       [(EITE cnd thn els)
        (EITE (rec cnd) (rec thn) (rec els))]
       [(ENop) expr]
       [_ (error 'rewrite-expr "unknown expr: ~v" expr)])]))

; return ctx[e1 := e2]
; (only method bodies need rewriting)
(define (rewrite-context ctx e1 e2)
  (Context-with-methods
   ctx
   (for/list ([addr/mtds (Context-methods ctx)])
     (cons (car addr/mtds)
           (for/list ([name/mtd (cdr addr/mtds)])
             (match-define (Method name args body) (cdr name/mtd))
             (cons (car name/mtd)
                   (Method name args (rewrite-expr body e1 e2))))))))
