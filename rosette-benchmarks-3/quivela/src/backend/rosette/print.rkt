#lang racket

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

(require (only-in rosette union-contents union?) "lang.rkt")
(provide print-expr print-value expr-to-string value-to-string)

(define (print-value value)
  (if (union? value)
      (let ([vals (map cdr (union-contents value))])
        (display "{ ")
        (for ([v vals][n (in-naturals)])
          (when (> n 0) (display ", "))
          (display (value-to-string v)))
        (display " }"))
      (match value
        [(Int n) (display n)]
        [(Ref a) (display "Ref(")
                 (display a)
                 (display ")")]
        [(Tuple elts) (display "<")
                      (for ([(l i) (in-indexed elts)])
                        (when (> i 0)
                          (display ", "))
                        (print-value l))
                      (display ">")]
        [(Map elts) (display "{")
                    (for ([(pr i) (in-indexed elts)])
                      (when (> i 0) (display ", "))
                      (print-value (car pr))
                      (display ": ")
                      (print-value (cdr pr)))
                    (display "}")]
        [(Nil)   (display "nil")]
        [(Error msg expr) (display "<error: ")
                          (display msg)
                          (display " @ ")
                          (if (Expr? expr)
                              (print-expr expr)
                              (display expr))
                          (display ">")]
        [_       (display value)])))

(define (value-to-string val)
  (with-output-to-string
    (thunk (print-value val))))


(define (print-expr expr)
  (match expr
    [(EVar x) (display x)]
    [(EConst v) (print-value v)]
    [(ETuple elts)
     (display "<")
     (for ([(l i) (in-indexed elts)])
       (when (> i 0)
         (display ", "))
       (print-expr l))
     (display ">")]
    [(ESeq e1 e2) (print-expr e1)
                  (display "; ")
                  (print-expr e2)]
    [(ECVar obj name idx)
     (unless (equal? obj (EConst (Nil)))
       (print-expr obj)
       (display "."))
     (display name)
     (unless (equal? idx (EConst (Nil)))
       (display "[")
       (print-expr idx)
       (display "]"))]
    [(ENew locals body)
     (display "new (")
     (for ([(l i) (in-indexed locals)])
       (when (> i 0)
         (display ", "))
       (display (Init-name l))
       (unless (equal? (Init-val l) (EConst (Nil)))
         (display "=")
         (print-expr (Init-val l))))
     (display ") { ")
     (print-expr body)
     (display " }; ")]
    [(EMethod name args body)
     (display name)
     (display "(")
     (for ([(a i) (in-indexed args)])
       (when (> i 0)
         (display ", "))
       (display (EVar-name a)))
     (display ") { ")
     (print-expr body)
     (display " }; ")]
    [(EAssign lhs rhs)
     (print-expr lhs)
     (display " = ")
     (print-expr rhs)]
    [(ECall obj name args)
     (cond
       [(and (equal? obj (EConst (Nil))) (not (equal? (Is_Builtin_Arity name) -1)))
        (define arity (Is_Builtin_Arity name))
        (cond
          [(and (equal? arity 1) (> (length args) 0))
           (display name)
           (print-expr (car args))]
          [(and (equal? arity 2) (> (length args) 1))
           (print-expr (car args))
           (display " ")
           (display name)
           (display " ")
           (print-expr (cadr args))]
          [(equal? arity 0)
           (display name)
           (display "()")]
          [else (error 'print-expr "what is this? ~v" expr)])]
       [else
        (unless (equal? obj (EConst (Nil)))
          (print-expr obj)
          (display "."))
        (display name)
        (display "(")
        (for ([(a i) (in-indexed args)])
          (when (> i 0)
            (display ", "))
          (print-expr a))
        (display ")")])]
    [(EITE cnd thn els)
     (display "if ")
     (print-expr cnd)
     (display " { ")
     (print-expr thn)
     (display " } ")
     (unless (equal? els (ENop))
       (display "else { ")
       (print-expr els)
       (display " } "))]
    [(ENop) (void)]
    [_ (error 'print-expr "what is this? ~v" expr)]))

(define (expr-to-string expr)
  (with-output-to-string
    (thunk (print-expr expr))))
