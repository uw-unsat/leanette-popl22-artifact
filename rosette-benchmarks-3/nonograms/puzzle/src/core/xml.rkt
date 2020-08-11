#lang racket
; functions for constructing X-expressions that have a nicer syntax and can check for errors

(provide
  xexp
  xexpr->html-string
  write-html-to-file)

(require
  (for-syntax syntax/parse)
  html-writing)

(define (check-xexpr expr)
  (local-require xml)
  ;(displayln expr)
  (cond
   [(integer? expr) (format "~a" expr)]
   [(symbol? expr) (symbol->string expr)]
   [else (and (validate-xexpr expr) expr)]))

(define (check-string expr)
  (cond
   [(string? expr) expr]
   ; assume integers were meant to be text and convert them to strings
   [(integer? expr) (format "~a" expr)]
   [(symbol? expr) (symbol->string expr)]
   [else (error (format "Expected a string for XML attribute value. Got ~a." expr))]))

; X-expression literal which allows for attributes to be specified with keywords.
; Can use unquote to include arbitrary content, which will be validated using validate-xexpr.
(define-syntax (xexp stx)
  (define-splicing-syntax-class attribute
    #:description "xml attribute"
    #:literals (unquote)
    (pattern
      (~seq kw:keyword value:str)
      #:with name (datum->syntax #'kw (string->symbol (keyword->string (syntax->datum #'kw)))))
    (pattern
      (~seq kw:keyword (unquote x:expr))
      #:with name (datum->syntax #'kw (string->symbol (keyword->string (syntax->datum #'kw))))
      #:with value #'(unquote (check-string x)))
    (pattern
      (~seq kw:keyword i:integer)
      #:with name (datum->syntax #'kw (string->symbol (keyword->string (syntax->datum #'kw))))
      #:with value (datum->syntax #'i (format "~a" (syntax->datum #'i)))))
  (define-splicing-syntax-class element
    #:description "xml element"
    (pattern
      (element:id attr:attribute ... subelem:content ...)
      #:with content #`(element ((attr.name attr.value) ...) subelem.content ...)))
  (define-splicing-syntax-class content
    #:description "xml content"
    #:literals (unquote unquote-splicing)
    (pattern (unquote x:expr) #:with content #'(unquote (check-xexpr x)))
    (pattern (unquote-splicing x:expr) #:with content #'(unquote-splicing (map check-xexpr x)))
    (pattern x:element #:with content #'x.content)
   ; assume integers were meant to be text and convert them to strings
    (pattern x:integer #:with content (datum->syntax #'x (format "~a" (syntax->datum #'x))))
    (pattern x:str #:with content #'x))
  (syntax-parse stx
   [(_ element:id attr:attribute ... others:content ...) #'`(element ((attr.name attr.value) ...) others.content ...)]))

; huzzah for two different xml representations
; in our case the main thing we care about with converstion is putting @'s in front of the attribute lists
(define (xexpr->sxml xexpr)
  (match xexpr
   [(cons (? symbol? elem) tail)
    (cons elem (map xexpr->sxml tail))]
   [(list attrs ...)
    (cons '@ xexpr)]
   [x x]))


; xexpr? -> string?
(define (xexpr->html-string doc)
  (format "<!DOCTYPE html>\n~a\n" (xexp->html (xexpr->sxml doc))))

(define (write-html-to-file filename doc)
  (call-with-output-file filename #:exists 'truncate (λ (out) (write-html (xexpr->sxml doc) out))))

