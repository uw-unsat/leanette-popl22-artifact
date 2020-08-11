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
(struct object ([classid][objectid] [size #:auto #:mutable] [contents #:auto #:mutable] [vec #:auto #:mutable] [id #:auto #:mutable] [value #:auto #:mutable] [@hour #:auto #:mutable] [@min #:auto #:mutable] [@sec #:auto #:mutable] [@hours #:auto #:mutable] ) #:transparent #:auto-value (void))
 
;;; ARGUMENT DEFINITIONS:
  ; Initialize symbolic inputs to method 
  ; Initialize h of type Bignum or Fixnum
(define h (begin (define-symbolic* h integer?) (int h)))

  ; Initialize struct self of type BusinessTime::BusinessHours
(define self
(let ([self (object 7 (new-obj-id))])
(define @hours (begin (define-symbolic* @hours integer?) (int @hours)))

(set-object-@hours! self @hours)
self))

;;; FUNCTION DEFINITIONS:
(define (BusinessTime::BusinessHours_inst_initialize self hours #:block [BLK (void)])
	(let ()
	(begin
(begin (set-object-@hours! self hours) (object-@hours self)) (return self))))

;;;RETURN VALUE:
(define s (BusinessTime::BusinessHours_inst_initialize self h))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? s) (Integer_inst_== (object-@hours self) h ))))

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
BusinessTime::ParsedTime->6
BusinessTime::BusinessHours->7
|#
