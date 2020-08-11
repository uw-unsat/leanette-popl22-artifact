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
  ; Initialize x of type Float
(define x (begin (define-symbolic* real_x real?) (float real_x)))

  ; Initialize struct self of type Unitwise::Functional
(define self
(let ([self (object 6 (new-obj-id))])
self))

;;; FUNCTION DEFINITIONS:
(define (Unitwise::Functional_from_degf self x #:block [BLK (void)])
	(let ()
	(return (Float_inst_* (Float_inst_/ (float 5.0) (float 9.0) ) (begin
	(Float_inst_+ x (float 459.67) )
	) ))))

(define (Unitwise::Functional_to_degf self x #:block [BLK (void)])
	(let ()
	(return (Float_inst_- (Float_inst_/ (Float_inst_* (float 9.0) x ) (float 5.0) ) (float 459.67) ))))
;;;RETURN VALUE:
(define res (Unitwise::Functional_from_degf self x))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? res) (Float_inst_== x (Unitwise::Functional_to_degf self res ) ))))

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
Unitwise::Functional->6
|#
