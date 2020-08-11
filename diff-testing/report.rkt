#lang racket


(require text-table
         "metric.rkt"
         "color.rkt")

(define (avg xs #:precision [precision 0])
  (match xs
    ['() +nan.0]
    [_ (~r (/ (apply + xs) (length xs)) #:precision precision)]))

(define (add-comma n)
  (match n
    [+nan.0 (number->string n)]
    [_ (define s (if (string? n)
                     n
                     (number->string n)))
       (string-append*
        (reverse
         (for/list ([digit (reverse (string->list s))] [i (in-naturals)])
           (cond
             [(zero? i) (string digit)]
             [(zero? (modulo i 3)) (string digit #\,)]
             [else (string digit)]))))]))

(define all-random-progs
  (with-input-from-file "workspace/log.rktd"
    (λ () (for/list ([row (in-port)]) row))))

(define-values (random-progs bad-random-progs)
  (partition (λ (x) (eq? (metric-result x) #t)) all-random-progs))

(for ([bad-prog bad-random-progs])
  (cprintf 'red "program at ~a fails differential testing because ~a"
           (metric-path bad-prog)
           (match (metric-result bad-prog)
             [#f "Leanette and Rosette* disagree"]
             ['lean-out-of-fuel "Leanette runs out of fuel"]
             ['lean-fatal-error "Leanette has a fatal error"]
             ['rosette-timeout "Rosette* timeout"]
             ['lean-timeout "Leanette timeout"]))
  (newline))

(define sorted (sort random-progs < #:key metric-size))

(define xs
  (for/fold ([result '()] [group '()] #:result (reverse (cons group result)))
            ([x sorted])
    (define ast-size (metric-size x))
    (match group
      ['() (values result (cons x group))]
      [(cons latest _)
       (define latest-size (metric-size latest))
       (cond
         [(= latest-size ast-size) (values result (cons x group))]
         [(> (length group) 1000)
          (values (cons (reverse group) result) (list x))]
         [else
          (values result (cons x group))])])))

(define (->s x) (/ x 1000))

(define not-trivial-lean? (compose1 not lean-metric-trivial? metric-lean))
(define not-trivial-rosette? (compose1 not rosette-metric-trivial? metric-rosette))

(define (safe-max xs #:precision [precision #f])
  (match xs
    ['() +nan.0]
    [_
     (define out (apply max xs))
     (cond
       [precision (~r out #:precision precision)]
       [else out])]))

(define (safe-min xs)
  (match xs
    ['() +nan.0]
    [_ (apply min xs)]))

(print-table
 (cons
  (list "Range" "Count" "Avg"
        "(Leanette state) Sym" "Max" "Avg"
        "(Rosette* state) Sym" "Max" "Avg"
        "(Leanette time) Max" "Avg"
        "(Rosette time) Max" "Avg"
        "Validated?")
  (for/list ([group xs])
    (append (list (format "~a - ~a" (safe-min (map metric-size group)) (safe-max (map metric-size group))))
            (map add-comma
                 (list (length group)
                       (avg (map metric-size group))
                       (count not-trivial-lean? group)
                       (safe-max (map (compose1 lean-metric-size metric-lean) (filter not-trivial-lean? group)))
                       (avg (map (compose1 lean-metric-size metric-lean) (filter not-trivial-lean? group)))
                       (count not-trivial-rosette? group)
                       (safe-max (map (compose1 rosette-metric-size metric-rosette) (filter not-trivial-rosette? group)))
                       (avg (map (compose1 rosette-metric-size metric-rosette) (filter not-trivial-rosette? group)))))
            (list (safe-max (map (compose1 ->s lean-metric-time metric-lean) group) #:precision '(= 1))
                  (avg (map (compose1 ->s lean-metric-time metric-lean) group) #:precision '(= 1))
                  (safe-max (map (compose1 ->s rosette-metric-time metric-rosette) group) #:precision '(= 1))
                  (avg (map (compose1 ->s rosette-metric-time metric-rosette) group) #:precision '(= 1))
                  "✓")))))
