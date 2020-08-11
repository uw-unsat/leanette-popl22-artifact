;;; TODO: how to determine class of resulting object?
(define (not_eq x y) (return (not (equal? x y))))
(define (divmod x y) (return (Array_literal (list (quotient x y) (remainder x y)))))
(define Fixnum_ID 2)
#|
(define (Fixnum_inst_+ self arg) (let* ([val1 (object-value self)][val2 (object-value arg)][res (+ val1 val2)][res_obj (object Fixnum_ID)]) (begin (set-object-value! res_obj res) (return res_obj))))
(define (Fixnum_inst_- self arg) (let* ([val1 (object-value self)][val2 (object-value arg)][res (- val1 val2)][res_obj (object Fixnum_ID)]) (begin (set-object-value! res_obj res) (return res_obj))))
(define (Fixnum_inst_* self arg) (let* ([val1 (object-value self)][val2 (object-value arg)][res (* val1 val2)][res_obj (object Fixnum_ID)]) (begin (set-object-value! res_obj res) (return res_obj))))
|#
