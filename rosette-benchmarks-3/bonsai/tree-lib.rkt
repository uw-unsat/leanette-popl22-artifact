#lang rosette

(provide
    echo-union

    new-boolean!
    new-enum!
    nonterminals!
    null*
    symbol->enum
    enum->symbol
    treemap
    expression->enumtree
    enumtree->expression

    weigh-formula!
    current-weight!

    table-add
    table-find

    syntax-matches?
    binary-tree!

    tree-match
    tree-match-test)

(require "bounded.rkt")
;(current-bound! 20)

; Display a symbolic value in a large tree form
(define (echo-union u)
    (if (union? u)
        (map
            (lambda (p)
                (list
                      ':guard
                      (echo-union (car p))
                      (echo-union (cdr p))))
            (union-contents u))
        (if (term? u)
            (list ':literal
                  (term->datum u))
            (if (pair? u)
                (list
                    ':cons
                    (echo-union (car u))
                    (echo-union (cdr u)))
                (list ':: u)))))

; Bitvector-encoding for enums
(define bv-width 32)
(define enum-idx 0)
(define enum-dict '())

(define (new-boolean!)
    (define-symbolic* bool-val boolean?)
    bool-val)

(define (new-enum!)
    (define-symbolic* enum-val (bitvector bv-width))
    enum-val)

(define (new-symbol! sym)
    (begin
        (set! enum-idx (+ 1 enum-idx))
        (define ret (bv (expt 2 enum-idx) bv-width))
        (set! enum-dict (cons (cons sym ret) enum-dict))
        ret))

(define null* (new-symbol! '()))

(define (nonterminals! n)
    (void (map new-symbol! n)))

(define (symbol->enum sym)
    (cdar (filter (λ (x) (equal? (car x) sym)) enum-dict)))

(define (enum->symbol e)
    (define q (filter (λ (x) (equal? (cdr x) e)) enum-dict))
    (if (null? q) '___ (caar q)))

(define (treemap f tree)
    (if (pair? tree)
        (cons (treemap f (car tree))
              (treemap f (cdr tree)))
        (f tree)))

(define (expression->enumtree e)
    (treemap symbol->enum e))

(define (enumtree->expression e)
    (treemap enum->symbol e))


; Find the size of a formula
(require racket/match)
(define weigh-cache (make-hasheq))
(define (weigh-formula f)
    (if (hash-has-key? weigh-cache f) 0
        (begin
            (hash-set! weigh-cache f 'cheese)
        (if (union? f)
            (foldl + 0 (map (λ (c) (+ (weigh-formula (car c)) (weigh-formula (cdr c)))) (union-contents f)))
            (match f
                [(constant id type) 1]
                [(expression type children ...)
                 (foldl + 0 (map weigh-formula children))]
                [(cons a b) (+ (weigh-formula a) (weigh-formula b))]
                [_ 1])))))

(define (weigh-formula! f)
    (begin
        (hash-clear! weigh-cache)
        (weigh-formula f)))

; Current assertions size
(define (current-weight!)
    (foldl + 0 (map weigh-formula! (asserts))))

; Assert syntax ok
(define (table-add table key value)
    (cons (cons key value) table))


; Naive table find
(define/rec (table-find table key)
    (if (not (pair? table)) #f
        (if (equal? (caar table) key)
            (cdar table)
            (table-find (cdr table) key))))

; Don't panic
(define (table-find* table key)
    (if (not (pair? table)) #f
        (if (equal? (caar table) key)
            (cdar table)
            (table-find* (cdr table) key))))

(define (syntax-matches? stx pattern tree)
    (for/all [(tree tree)]
        (if (pair? pattern)
            (if (pair? tree)
                (and (syntax-matches? stx (car pattern) (car tree))
                     (syntax-matches? stx (cdr pattern) (cdr tree)))
                #f)
            (let [(rules (table-find* stx pattern))]
                 (if rules
                    (ormap (λ (pat) (syntax-matches? stx pat tree)) rules)
                    (equal? (symbol->enum pattern) tree)))))
    )

; Make a binary tree
(define (binary-tree! depth)
    (begin
        (assert (> depth 0))
        (if (new-boolean!)
            (new-enum!)
            (cons (binary-tree! (- depth 1))
                  (binary-tree! (- depth 1))))))



(define (tree-match tree . patterns)
    (begin
        (assert (pair? patterns) "Tree match failure!")
        (define q (tree-match-test tree (car patterns)))
        (if q
            (apply (cadr patterns) q)
            (apply tree-match (cons tree (cddr patterns))))))

(define (tree-match-test tree pattern)
    (cond [(and (pair? tree) (pair? pattern))
           (let [(a (tree-match-test (car tree) (car pattern)))
                 (b (tree-match-test (cdr tree) (cdr pattern)))]
                (and a b (append a b)))]
          [(and (not (pair? tree)) (pair? pattern)) #f]
          [(eq? pattern '_) (list tree)]
          [#t
           (if (equal? (symbol->enum pattern) tree) '() #f)]))




