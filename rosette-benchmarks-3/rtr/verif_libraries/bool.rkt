(define (bool x)
  (let ([ret (object (object BOOL_ID (new-obj-id)))])
    (begin (set-object-value! ret x)
           (return ret))))

(define (Boolean_inst_== x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)])
    (return (bool (eq? val1 val2)))))

(define (Boolean_inst_&& x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)])
    (return (bool (and val1 val2)))))

(define (Boolean_inst_|| x y)
  (let ([val1 (object-value x)]
        [val2 (object-value y)])
    (return (bool (or val1 val2)))))

(define (Boolean_inst_! x)
  (let ([val1 (object-value x)])
    (return (bool (not val1)))))

