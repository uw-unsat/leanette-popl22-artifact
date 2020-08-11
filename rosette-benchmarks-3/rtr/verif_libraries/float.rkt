(define (float x)
  (let ([ret (object FLOAT_ID x)])
    (begin (set-object-value! ret x)
           (return ret))))

;; Comparison Operators

(define (Float_inst_== x y)
  (if (or (not (object? y)) (not (object? x))) (return (eq? x y))
      (let* ([val1 (object-value x)]
             [val2 (object-value y)]
             [num2 (if (bv? val2) (bitvector->integer val2) val2)])
        (return (= val1 num2)))))

(define (Float_inst_< x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (< val1 num2))))

(define (Float_inst_<= x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (<= val1 num2))))

(define (Float_inst_> x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (> val1 num2))))

(define (Float_inst_>= x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (>= val1 num2))))

;; Arithmetic Operators

(define (Float_inst_-@ x)
  (let ([val1 (object-value x)])
    (return (float (- 0 val1)))))

(define (Float_inst_+ x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (float (+ val1 num2)))))

(define (Float_inst_- x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (float (- val1 num2)))))

(define (Float_inst_* x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (float (* val1 num2)))))

(define (Float_inst_/ x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (float (/ val1 num2)))))

(define (Float_inst_remainder x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (float (remainder val1 num2)))))

(define (Float_inst_% x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (float (modulo val1 num2)))))

(define (Float_inst_abs x)
  (let ([val1 (object-value x)])
    (return (float (if (> val1 0) val1 (- val1))))))

(define (Float_inst_** x y)
  (let* ([val1 (object-value x)]
         [val2 (object-value y)]
         [num2 (if (bv? val2) (bitvector->integer val2) val2)])
    (return (float (expt val1 num2)))))
