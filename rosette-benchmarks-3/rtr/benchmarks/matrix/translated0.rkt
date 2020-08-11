#lang rosette
(require "../../verif_libraries/ivl.rkt")

(require racket/include)(require racket/undefined)
(define USE_BV false)
(define BVSIZE 6)(include (file "../../verif_libraries/integer.rkt"))
(include (file "../../verif_libraries/hash.rkt"))
(include (file "../../verif_libraries/bool.rkt"))
(include (file "../../verif_libraries/array.rkt"))
(include (file "../../verif_libraries/float.rkt"))
(include (file "../../verif_libraries/fixnum.rkt"))
(include (file "../../verif_libraries/helper.rkt"))
(include (file "../../verif_libraries/ids.rkt"))
(include (file "../../verif_libraries/basicobject.rkt"))
(include (file "../../verif_libraries/kernel.rkt"))


;;; OBJECT STRUCT:
(struct object ([classid][objectid] [size #:auto #:mutable] [contents #:auto #:mutable] [vec #:auto #:mutable] [id #:auto #:mutable] [value #:auto #:mutable] [@column_count #:auto #:mutable] [@rows #:auto #:mutable] ) #:transparent #:auto-value (void))
 
;;; ARGUMENT DEFINITIONS:
  ; Initialize symbolic inputs to method 
  ; Initialize l of type Matrix
(define l
(let ([l (object 6 (new-obj-id))])
(define @column_count (begin (define-symbolic* @column_count integer?) (int @column_count)))

(define @rows
(new-symbolic-array
(lambda (__IDX)
(define __CONSTRUCTED_ELE
(new-symbolic-array
(lambda (__IDX)
(define __CONSTRUCTED_ELE (begin (define-symbolic* __CONSTRUCTED_ELE integer?) (int __CONSTRUCTED_ELE)))

(return __CONSTRUCTED_ELE))))
(return __CONSTRUCTED_ELE))))
(set-object-@column_count! l @column_count)
(set-object-@rows! l @rows)
l))
  ; Initialize r of type Matrix
(define r
(let ([r (object 6 (new-obj-id))])
(define @column_count (begin (define-symbolic* @column_count integer?) (int @column_count)))

(define @rows
(new-symbolic-array
(lambda (__IDX)
(define __CONSTRUCTED_ELE
(new-symbolic-array
(lambda (__IDX)
(define __CONSTRUCTED_ELE (begin (define-symbolic* __CONSTRUCTED_ELE integer?) (int __CONSTRUCTED_ELE)))

(return __CONSTRUCTED_ELE))))
(return __CONSTRUCTED_ELE))))
(set-object-@column_count! r @column_count)
(set-object-@rows! r @rows)
r))
  ; Initialize struct self of type Matrix
(define self
(let ([self (object 6 (new-obj-id))])
(define @column_count (begin (define-symbolic* @column_count integer?) (int @column_count)))

(define @rows
(new-symbolic-array
(lambda (__IDX)
(define __CONSTRUCTED_ELE
(new-symbolic-array
(lambda (__IDX)
(define __CONSTRUCTED_ELE (begin (define-symbolic* __CONSTRUCTED_ELE integer?) (int __CONSTRUCTED_ELE)))

(return __CONSTRUCTED_ELE))))
(return __CONSTRUCTED_ELE))))
(set-object-@column_count! self @column_count)
(set-object-@rows! self @rows)
self))

;;; FUNCTION DEFINITIONS:
(define (Matrix_* self  l r #:block [BLK (void)])
	(let ([rows 'undefined][range 'undefined][start 'undefined])
	(begin
	(begin (set! rows (Array_inst_initialize (object 2 (new-obj-id)) (Matrix_inst_row_count l ) #:block (lambda (i)
(return (Array_inst_initialize (object 2 (new-obj-id)) (Matrix_inst_column_count r ) #:block (lambda (j)
(begin
	(begin (set! range (Array_inst_initialize (object 2 (new-obj-id)) (Matrix_inst_column_count l ) #:block (lambda (x)
(return x))))  range)
	
	
	(begin (set! start (int 0))  start)
	(return (Enumerable_inst_inject range start #:block (lambda ( vij k)
(return (Integer_inst_+ vij (Integer_inst_* (Matrix_inst_ref l i k ) (Matrix_inst_ref r k j ) ) )))))
	)))))))  rows)
	
	(return (Matrix_inst_initialize (object 6 (new-obj-id)) rows (Matrix_inst_column_count r ) ))
	)))

(define (Matrix_inst_column_count self  #:block [BLK (void)])
	(let ()
	(return (object-@column_count self))))

(define (Matrix_inst_ref self  i j #:block [BLK (void)])
	(let ()
	(return (Array_inst_ref (Array_inst_ref (object-@rows self) i ) j ))))

(define (Matrix_inst_row_count self  #:block [BLK (void)])
	(let ()
	(return (Array_inst_size (object-@rows self) ))))

(define (Matrix_inst_initialize self  rows column_count #:block [BLK (void)])
	(let ()
	(begin
(begin
	(begin (set-object-@rows! self rows) (object-@rows self))
	(begin (set-object-@column_count! self column_count) (object-@column_count self))
	) (return self))))

(define (Matrix_inst_valid_matrix? self  #:block [BLK (void)])
	(let ([each_row_valid 'undefined])
	(begin
	
	(begin (set! each_row_valid true)  each_row_valid)
	(Array_inst_each (object-@rows self) #:block (lambda (row)
(begin (set! each_row_valid (and each_row_valid (begin
	(Integer_inst_== (Array_inst_size row ) (Matrix_inst_column_count self ) )
	) ))  (return each_row_valid))))
	(return (and (Integer_inst_>= (Matrix_inst_column_count self ) (int 0) ) each_row_valid ))
	)))

(define (Matrix_inst_valid_matrix_of_size? self  num_rows num_cols #:block [BLK (void)])
	(let ()
	(return (and (Matrix_inst_valid_matrix? self ) (Matrix_inst_of_size? self num_rows num_cols ) ))))

(define (Matrix_inst_of_size? self  num_rows num_cols #:block [BLK (void)])
	(let ()
	(return (and (Integer_inst_== (Matrix_inst_row_count self ) num_rows ) (Integer_inst_== (Matrix_inst_column_count self ) num_cols ) ))))

;;;RETURN VALUE:
(define res (Matrix_* self l r))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and (Matrix_inst_valid_matrix? l ) (Matrix_inst_valid_matrix? r ) )) #:guarantee (assert (unless (stuck? res) (Matrix_inst_valid_matrix_of_size? res (Matrix_inst_row_count l ) (Matrix_inst_column_count r ) ))))

#|
Class Name->Class ID
Hash->0
Class->1
Array->2
Fixnum->3
Bignum->3
Integer->3
Float->4
Boolean->5
Matrix->6
|#
