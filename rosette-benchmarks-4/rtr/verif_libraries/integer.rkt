(define (int x)
  (let ([ret (object INT_ID x)]
        [val (if USE_BV (if (bv? x) x (integer->bitvector x (bitvector BVSIZE))) (if (bv? x) (bitvector->integer x) x))])
    (begin (set-object-value! ret val)
           (return ret))))

(define (prim_int x)
  (cond [(integer? x) (return x)]
        [(bv? x) (return (bitvector->integer x))]
        [else
         (let ([val (object-value x)])
           (if (integer? val)
               (return val)
               (return (bitvector->integer val))))]))

;; Comparison Operators

(define (Integer_inst_== x y)
  (if (or (not (object? y)) (not (object? x))) (return (eq? x y))
      (let ([val1 (object-value x)]
            [val2 (object-value y)]
            [id2 (object-classid y)])
        (if (integer? val1)
            (return (= val1 val2))
            (cond [(= id2 INT_ID) (return (bveq val1 val2))]
                  [(= id2 FLOAT_ID) (let ([int1 (bitvector->integer val1)]) (return (= int1 val2)))]
                  [else (return false)])))))

(define (Integer_inst_!= x y)
  (not (Integer_inst_== x y)))

(define (Integer_inst_< x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (return (< val1 val2))
        (if (= id2 INT_ID)
            (return (bvslt val1 val2))
            (let ([int1 (bitvector->integer val1)]) (return (< int1 val2)))))))

(define (Integer_inst_<= x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (return (<= val1 val2))
        (if (= id2 INT_ID)
            (return (bvsle val1 val2))
            (let ([int1 (bitvector->integer val1)]) (return (<= int1 val2)))))))

(define (Integer_inst_> x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (return (> val1 val2))
        (if (= id2 INT_ID)
            (return (bvsgt val1 val2))
            (let ([int1 (bitvector->integer val1)]) (return (> int1 val2)))))))

(define (Integer_inst_>= x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (return (>= val1 val2))
    (if (= id2 INT_ID)
        (return (bvsge val1 val2))
        (let ([int1 (bitvector->integer val1)]) (return (>= int1 val2)))))))

;; Arithmetic Operators

(define (Integer_inst_-@ x)
  (let ([val1 (object-value x)])
    (if (integer? val1)
        (return (int (- 0 val1)))
        (return (int (bvneg val1))))))

(define (Integer_inst_+ x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (if (= id2 FLOAT_ID) (return (int (+ val1 val2))) (return (float (+ val1 val2))))
        (cond
          [(= id2 INT_ID) (return (int (bvadd val1 val2)))]
          [(= id2 FLOAT_ID)
           (let ([int1 (bitvector->integer val1)])
             (return (float (+ int1 val2))))]
          [else (print "Int arithmetic with unexpected type.")]))))

(define (Integer_inst_- x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (if (= id2 FLOAT_ID) (return (int (- val1 val2))) (return (float (- val1 val2))))
        (cond
          [(= id2 INT_ID) (return (int (bvsub val1 val2)))]
          [(= id2 FLOAT_ID)
           (let ([int1 (bitvector->integer val1)])
             (return (float (- int1 val2))))]
          [else (print "Int arithmetic with unexpected type.")]))))

(define (Integer_inst_* x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (if (= id2 FLOAT_ID) (return (int (* val1 val2))) (return (float (* val1 val2))))
        (cond
          [(= id2 INT_ID) (return (int (bvmul val1 val2)))]
          [(= id2 FLOAT_ID)
           (let ([int1 (bitvector->integer val1)])
             (return (float (* int1 val2))))]
          [else (print "Int arithmetic with unexpected type.")]))))

(define (Integer_inst_/ x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (if (= id2 FLOAT_ID) (return (int (/ val1 val2))) (return (float (/ val1 val2))))
        (cond
          [(= id2 INT_ID) (return (int (bvsdiv val1 val2)))]
          [(= id2 FLOAT_ID)
           (let ([int1 (bitvector->integer val1)])
             (return (float (/ int1 val2))))]
          [else (print "Int arithmetic with unexpected type.")]))))

(define (Integer_inst_remainder x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (if (= id2 FLOAT_ID) (return (int (remainder val1 val2))) (return (float (remainder val1 val2))))
        (cond
          [(= id2 INT_ID) (return (int (bvsrem val1 val2)))]
          [(= id2 FLOAT_ID)
           (let ([int1 (bitvector->integer val1)])
             (return (float (remainder int1 val2))))]   ;;TODO: remainder with float isn't allowed in Racket (unlike Ruby)
          [else (print "Int arithmetic with unexpected type.")]))))

(define (Integer_inst_% x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (if (= id2 FLOAT_ID) (return (int (modulo val1 val2))) (return (float (modulo val1 val2))))
        (cond
          [(= id2 INT_ID) (return (int (bvsmod val1 val2)))]
          [(= id2 FLOAT_ID)
           (let ([int1 (bitvector->integer val1)])
             (return (float (modulo int1 val2))))]
          [else (print "Int arithmetic with unexpected type.")]))))

(define (Integer_inst_abs x)
  (let* ([val1 (object-value x)])
    (if (integer? val1)
        (return (int (abs val1)))
        (let ([ret (if (bvsgt val1 (bv 0 BVSIZE)) val1 (bvneg val1))])
          (return (int ret))))))

(define (Integer_inst_divmod x y)
  (return (Array_literal (list (Integer_inst_/ x y) (Integer_inst_remainder x y)))))

(define (Integer_inst_** x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)]
        [id2 (object-classid y)])
    (if (integer? val1)
        (if (= id2 FLOAT_ID) (return (int (expt val1 val2))) (return (float (expt val1 val2))))
        (cond
          [(= id2 INT_ID) (return (int (pow_aux val1 val2)))]
          [(= id2 FLOAT_ID)
           (let ([int1 (bitvector->integer val1)])
             (return (float (expt int1 val2))))]
          [else (print "Int arithmetic with unexpected type.")]))))

(define (pow_aux x y)
  (cond
    [(bveq y (bv 0 BVSIZE)) 1]
    [(bveq y (bv 1 BVSIZE)) x]
    [else (bvmul x (pow_aux x (bvsub y 1)))]))

(define (Integer_inst_upto self limit #:block [BLK nil])
  (if (Integer_inst_> self limit)
      (return self)
      (begin
        (BLK self)
        (Integer_inst_upto (Integer_inst_+ self (int 1)) limit #:block BLK))))



