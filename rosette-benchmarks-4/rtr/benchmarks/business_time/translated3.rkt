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
  ; Initialize struct self of type Date
(define self
(let ([self (object 8 (new-obj-id))])
self))

;;; FUNCTION DEFINITIONS:
(define (Date_inst_week self  #:block [BLK (void)])
	(let ([cyw 'undefined])
	(begin
	(begin (set! cyw (Integer_inst_+ (begin
	(Integer_inst_/ (begin
	(Integer_inst_- (let ([self self])(begin(define d (int (Date_inst_yday (object-objectid self) )))(assume (and (Integer_inst_>= d (int 1) ) (Integer_inst_<= d (int 366) ) )) d)) (int 1) )
	) (int 7) )
	) (int 1) ))  cyw)
	(if (Integer_inst_== cyw (int 53) ) (begin (set! cyw (int 52))  cyw) (void))
	(return cyw)
	)))

(define-symbolic Date_inst_yday (~> integer? integer?))
;;;RETURN VALUE:
(define w (Date_inst_week self ))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? w) (and (Integer_inst_>= w (int 1) ) (Integer_inst_<= w (int 52) ) ))))

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
Date->8
|#