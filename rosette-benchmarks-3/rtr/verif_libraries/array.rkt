(define array-capacity 10)
(define nil (void))
(define id 2)

(define (new-symbolic-size)
  (define-symbolic* ary-size integer?)
  (assert (>= array-capacity ary-size))
  (assert (>= ary-size 0))
  (return (int ary-size)))

(define (new-symbolic-index size)
  (if USE_BV
      (begin
        (define-symbolic* b (bitvector BVSIZE))
        (assert (bvsge b (bv 0 BVSIZE)))
        (assert (bvsgt (integer->bitvector size (bitvector BVSIZE)) b))
        (return (int b)))
      (begin
        (define-symbolic* b integer?)
        (assert (> size b))
        (assert (>= b 0))
        (return (int b)))))

(define (new-symbolic-array [initializer (lambda (x) nil)])
  ; Create a new array of maximum capacity using the supplied populator lambda
  (define s (new-symbolic-size))
  (return (Array_new s #:block initializer)))

(define (array->list a) (return (take (vector->list (object-vec a)) (object-size a))))

(define (list->array l)
  (define ary (Array_new))
  (define (fill i l)
    (when (not (equal? l '()))
      (Array_inst_set ary (int i) (car l))
      (fill (+ i 1) (cdr l)))
    (return nil))
  (fill 0 l)
  (return ary))

(define (list-index lst val)
  (define (index-h lst i)
    (return (cond
              [(equal? lst '()) -1]
              [(equal? (car lst) val) i]
              [else (index-h (cdr lst) (+ i 1))])))
  (return (index-h lst 0)))

; This takes a block {|accumulator, element, index|} and is for native use ONLY
(define (Array_native_inst_fold self start #:block [BLK nil])
  (define size (prim_size self))
  (define (apply-helper index acc)
    (when (< index size)
      (apply-helper (+ index 1) (BLK acc (Array_inst_fetch self index) index)))
    (return nil))
  (return (apply-helper 0 start)))

;;;;;;;;;;;;;;;;;
; ARRAY METHODS ;
;;;;;;;;;;;;;;;;;

(define (Array_literal lst #:block [BLK nil])
  (return (list->array lst)))

(define (Array_new [size (int 0)] [fill nil] #:block [BLK nil])
    (return (Array_inst_initialize (object id (new-obj-id)) size fill #:block BLK)))

(define (Array_inst_initialize cls [size (int 0)] [fill nil] #:block [BLK nil])
  ; Create the object and set relevant fields
  (define self (object id (new-obj-id)))
  (let ([size (prim_int size)])
    (set-object-size! self size)
    (set-object-vec! self (make-vector array-capacity fill))

    ; If a block was provided, use it to populate the array
    (when (not (equal? BLK nil))
      ; Apply the block by way of the native fold, wrapping the passed function to discard acc and ele
      (Array_native_inst_fold self nil #:block (lambda (acc ele i) (return (Array_inst_set self (int i) (BLK i))))))
    ; Finally, return self
    (return self)))

;; For internal use only. Doesn't use bitvectors.
(define (prim_size self #:block [BLK nil]) (return (object-size self)))

(define (Array_inst_size self #:block [BLK nil])
  (return (int (object-size self))))

; This may be more robustly implemented in terms of something in ruby, not native code
; I think this because of the check for content equality.
; It is currently dependent on the implementation, but could be written as an each across a zip.
(define (Array_inst_eql? self other #:block [BLK nil])
  (return
    (or
      (eq? self other)
      (and
        (= (prim_size self) (prim_size other))
        (equal? (object-vec self) (object-vec other))))))

; This needs more complete behavior
; ONLY WORKS FOR SINGLE ARGUMENT
(define (Array_inst_fetch self index #:block [BLK nil])
  (return
    (if (< index (prim_size self))
      (vector-ref (object-vec self) index)
      nil)))

; This function represents []=
; ONLY SUPPORTS SINGLE ARGUMENT
(define (Array_inst_refassign self index value #:block [BLK nil])
  (let ([i (prim_int index)])
    (begin
      (if (> 0 i) (set! i (- (object-size self) 1)) (void))
      (define vec (object-vec self))
      (vector-set! (object-vec self) i value)
      (set-object-size! self (max (object-size self) (+ i 1)))
      (return value))))

(define (Array_inst_delete_at self ind #:block [BLK nil])
  (define vec (object-vec self))
  (let ([index (prim_int ind)])
  ; If the index is out of bounds, return nil. Otherwise, collapse.
  (return
    (if (or (<= (prim_size self) 0) (>= index (prim_size self)))
      nil
      (let ([deleted (vector-ref vec index)])
        (vector-copy! vec index vec (+ index 1) array-capacity)
        (vector-set! vec (- array-capacity 1) nil)
        (set-object-size! self (- (object-size self) 1))
        deleted)))))

(define (Array_inst_include? self value)
  (return (not (eq? (member value (array->list self)) #f))))

(define (Array_inst_index self value #:block [BLK nil])
  (return (list-index (array->list self) value)))

; Things below this line are just aliases
(define (Array_inst_ref self index #:block [BLK nil])
  (let ([i (prim_int index)])
    (begin

      (if (> 0 i) (if (> (object-size self) 0) (set! i (- (object-size self) 1)) (return (void))) (void))
      (return (Array_inst_fetch self i #:block BLK)))))

(define (Array_inst_set self index value #:block [BLK nil])
  (return (Array_inst_refassign self index value #:block BLK)))

; Things below this line can be converted to ruby code, not native code
(define (Array_inst_push self value #:block [BLK nil])
  (Array_inst_set self (int (object-size self)) value)
  (return self))

(define (Array_inst_<< self value #:block [BLK nil])
  (return (Array_inst_push self value)))

(define (Array_inst_pop self #:block [BLK nil])
  (return (Array_inst_delete_at self 0)))

(define (Array_inst_each self #:block [BLK nil])
  (let* ([lst (array->list self)]
         [mp (map BLK lst)]
         [arr (list->array mp)])
    (return arr)))

; This should be migrated to an Enumerable mixin file
(define (Enumerable_inst_inject self initial #:block [BLK nil])
  (let ([acc initial])
       (Array_inst_each
        self
        #:block (lambda (x) (set! acc (BLK acc x)) (return acc)))
       (return acc)))
