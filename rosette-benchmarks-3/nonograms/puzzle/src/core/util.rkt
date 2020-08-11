#lang racket

(provide (all-defined-out))

(define debug-print? (make-parameter #f))

(define (blankline)
  (when (debug-print?)
    (newline (current-output-port))
    (flush-output (current-output-port))))

(define (println x)
  (print x)
  (newline (current-output-port))
  (flush-output (current-output-port)))

(define (dprint x)
  (when (debug-print?)
    (println x)
    (flush-output)))

; TODO figure out why this is not working...
(define-syntax-rule (dprintf x ...)
  (when (debug-print?)
    (displayln (format x ...))))

(define (flatten-once lst)
  (apply append lst))

(define (take* lst at-most)
  (take lst (min (length lst) at-most)))

(define (hash-map-values f hsh)
  (define (update k h) (hash-update h k f))
  (foldl update hsh (hash-keys hsh)))

(define (update-box! bx fn)
  (set-box! bx (fn (unbox bx))))

; 'a -> 'b, 'a list -> 'a list list
; partitions a list into equivalence classes based on a given key function, using equal?.
; any elements a, b for which (equal? (keyfn a) (keyfn b)) will be in the same equivalence class
; like partition, only for multiple classes rather than 2.
(define (partition-by-key keyfn lst)
  (define hsh (make-hash))
  (for ([x lst])
    (hash-update! hsh (keyfn x) (λ (tl) (cons x tl)) '()))
  (hash-values hsh))

; 'a, 'a -> boolean?, 'a list -> 'a list list
; partitions a list into equivalence classes based on a pairwise test.
; any elements a, b for which (testfn? a b) will be in the same equivalence class.
; uses a minimal amount of invocations to testfn (which may  be n^2 in the worst case).
(define (partition-by-pairwise-test testfn lst)
  (define (foldfn elem partitions)
    ; check the new element against an arbitrary member of each existing class.
    ; if we find one, add it. if not, it's a new class
    (define added?
      (ormap
        (λ (class-box)
          (define class (unbox class-box))
          (cond
           [(testfn elem (first class))
            (set-box! class-box (cons elem class))
            #t]
           [else #f]))
        partitions))
    (if added?
        partitions
        (cons (box (list elem)) partitions)))
  (map unbox (foldl foldfn empty lst)))

(define (print-memory-usage)
  (printf "memory usage: ~aMB\n" (~r (/ (current-memory-use) (* 1024 1024)) #:precision 2)))

(define (print-time-delta start end)
  (define-values (mins secs) (quotient/remainder (- end start) 60))
  (printf "total run time: ~a:~a\n" mins (~a #:width 2 #:pad-string "0" #:align 'right secs)))

(define (choose-random lst)
  (list-ref lst (random (length lst))))

; struct? -> symbol?
(define (struct-name val)
  ; name has a "struct:" on the front so chop that off
  (string->symbol (substring (symbol->string (vector-ref (struct->vector val) 0)) 7)))

