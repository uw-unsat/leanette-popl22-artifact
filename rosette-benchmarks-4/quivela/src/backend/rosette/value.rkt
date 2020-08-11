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

(require rosette/lib/angelic (prefix-in $ (only-in racket member)))
(require "lang.rkt")
(provide ??Value ??Value-typed)

; Return an fresh unknown value,
; without allowing references to objects beyond maxAddr
(define MAX_VALUE_SIZE 3)  ; this is bounded model checking!
(define (??Value maxAddr [tuple-depth 1] [maps? #t] [current #f])
  (define refs (for/list ([i maxAddr]) (Ref i)))  ; all addrs below the maxAddr
  (define-symbolic* val integer?)
  (define options
    (append refs
            (if (> tuple-depth 0)
                (let ([max-tuple (for/list ([i MAX_VALUE_SIZE]) (??Value maxAddr (- tuple-depth 1) #f))])
                  (for/list ([i MAX_VALUE_SIZE]) (Tuple (take max-tuple (+ i 1)))))
                '())
            (if maps?
                (let ([elts (for/list ([i MAX_VALUE_SIZE]) (cons (??Value maxAddr tuple-depth #f) (??Value maxAddr tuple-depth #f)))])
                  (list (Map elts)))
                '())
            (list (Error "" #f) (Int val))))
  (when (and current (not ($member current options)))
    (set! options (append options (list current))))
  (apply choose* options))

(define (??Value-typed type)
  (match type
    [(list t1 ...)
     (Tuple (for/list ([t t1]) (??Value-typed t)))]
    [_ (??Value 0 0 #f)]))