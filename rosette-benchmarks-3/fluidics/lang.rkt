#lang rosette

(require rosette/lib/angelic)
(provide (all-defined-out))

(current-bitwidth #f)


(define height (make-parameter 5))
(define width  (make-parameter 5))


;; Grid data structure ---------------------------------------------------------

(define (make-grid)
  (build-vector (height) (lambda (i) (make-vector (width) #f))))

(define (grid-ref g pt)
  (assert (idx? pt))
  ;(printf "grid-ref ~a, ~a \n" (show g) (show pt))
  (vector-ref (vector-ref g (point-y pt)) (point-x pt)))
       
(define (grid-set! g pt val)
  (assert (idx? pt))
  ;(printf "grid-set! ~a, ~a, ~a\n" (show g) (show pt) (show val))
  (vector-set! (vector-ref g (point-y pt)) (point-x pt) val))

(define (show v)
  (cond [(union? v) `(union ,(equal-hash-code v) ,(union-values v))]
        [(vector? v) `(vector ,(vector-length v) ,(eq-hash-code v))] ; (apply vector (map show (vector->list v)))]
        [else v]))

;; -----------------------------------------------------------------------------


(struct point (y x)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "[~a,~a]" (point-y self) (point-x self)))])


(struct dir (oy ox name)
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "~a" (dir-name self)))]
  #:property prop:procedure
  (lambda (self pt) (point (+ (point-y pt) (dir-oy self))
                           (+ (point-x pt) (dir-ox self)))))


(define N (dir -1  0 "N"))
(define S (dir +1  0 "S"))
(define W (dir  0 -1 "W"))
(define E (dir  0 +1 "E"))

(define dirs (list N S W E))
(define (?dir) (apply choose* dirs))


(define (idx? pt)
  (let ([y (point-y pt)]
        [x (point-x pt)])
    (and (< -1 y (height)) (< -1 x (width)))))

(define (neighbors pt)
  (filter idx? (for/list ([dir dirs]) (dir pt))))


(struct inst (proc args)
  #:transparent
  #:reflection-name 'instruction
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "inst: ~s" (cons (object-name (inst-proc self)) (inst-args self))))])


;; Move the droplet from pt in the given direction.
(define (move g pt dir)
  (define droplet (grid-ref g pt))
  (define pt2 (dir pt))
  (grid-set! g pt #f)
  (grid-set! g pt2 droplet))


;; An unknown move instruction: move unknown point (y,x) in unknown direction.
(define (?move)
  (define-symbolic* y x integer?)
  (inst move (list (point y x) (?dir))))


;; Mix a droplet by moving it through its E neighbor and back.
(define (mix g pt)
  ; a b | pt should point to a, the dots should be clear, and the result
  ; . . | will be put in pt
  (let ([e  (E pt)]
        [se (S (E pt))]
        [s  (S pt)]
        [a (grid-ref g pt)]
        [b (grid-ref g (E pt))])
    (assert (and a b))
    (grid-set! g pt 'c)
    (grid-set! g e  'c)
    (for ([i (in-range 3)])
      (move g pt E)
      (move g e  S)
      (move g se W)
      (move g s  N))
    ))


;; Unknown mix instruction for an unknown point.
(define (?mix)
  (define-symbolic* y x integer?)
  (inst mix (list (point y x))))


;; Run an experiment.
;; * `init` takes one arg: the grid. Called to initialize the grid.
;; * `spec` takes one arg: the grid. The return value is the spec.
(define (synthesize-program init spec)
  (define sol (unsat))
  (define sketch #f)
  (for ([len (in-range 1 20)] #:when (unsat? sol))
    (define grid (make-grid))
    (init grid)
    (set! sketch (build-list len (lambda (i) (choose* (?mix) (?move)))))
    (for ([i sketch])
      (apply (inst-proc i) grid (inst-args i)))
    (set! sol (solve (assert (spec grid)))))
  (if (sat? sol)
      (evaluate sketch sol)
      sol))
  