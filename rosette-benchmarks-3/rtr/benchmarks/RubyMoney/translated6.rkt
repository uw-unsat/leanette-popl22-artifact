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
(struct object ([classid][objectid] [size #:auto #:mutable] [contents #:auto #:mutable] [vec #:auto #:mutable] [id #:auto #:mutable] [value #:auto #:mutable] ) #:transparent #:auto-value (void))
 
;;; ARGUMENT DEFINITIONS:
  ; Initialize symbolic inputs to method 
  ; Initialize struct self of type Money::Arithmetic
(define self
(let () (define-symbolic* classid integer?) (let ([self (object classid (new-obj-id))])
self))
)

;;; FUNCTION DEFINITIONS:
(define (Money::Arithmetic_inst_nonzero? self  #:block [BLK (void)])
	(let ()
	(if (Integer_inst_!= (let ([self self])(begin(define tmpname23 (int (Money::Arithmetic_inst_fractional (object-objectid self) )))tmpname23)) (int 0) ) (return self) (return (void)))))

(define-symbolic Money::Arithmetic_inst_fractional (~> integer? integer?))
;;;RETURN VALUE:
(define out (Money::Arithmetic_inst_nonzero? self ))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? out) (if (Kernel_inst_nil? out ) (Integer_inst_== (let ([self self])(begin(define tmpname24 (int (Money::Arithmetic_inst_fractional (object-objectid self) )))tmpname24)) (int 0) ) (void)))))

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
Money::Arithmetic->6
::Money->7
|#
