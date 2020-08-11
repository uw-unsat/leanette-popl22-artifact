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
(define (Date_inst_fiscal_year self  #:block [BLK (void)])
	(let ()
	(if (Integer_inst_>= (let ([self self])(begin(define m (int (Date_inst_month (object-objectid self) )))(assume (and (Integer_inst_>= m (int 1) ) (Integer_inst_<= m (int 12) ) )) m)) (let ([tmp2 (Date_inst_fiscal_month_offset self )]) (begin (assume (not (stuck? tmp2))) tmp2)) ) (return (Integer_inst_+ (let ([self self])(begin(define y (int (Date_inst_year (object-objectid self) )))y)) (int 1) )) (return (let ([self self])(begin(define y (int (Date_inst_year (object-objectid self) )))y))))))

(define-symbolic Date_inst_month (~> integer? integer?))
(define (Date_inst_fiscal_month_offset self  #:block [BLK (void)])
	(let ()
	(return (let ([self (let ([tmp (object 1 9)]) (begin (set-object-id! tmp 9) tmp))])(begin(define fm (int (BusinessTime::Config_inst_fiscal_month_offset (object-objectid self) )))(assume (and (Integer_inst_>= fm (int 1) ) (Integer_inst_<= fm (int 12) ) )) fm)))))
(define-symbolic BusinessTime::Config_inst_fiscal_month_offset (~> integer? integer?))
(define-symbolic Date_inst_year (~> integer? integer?))
;;;RETURN VALUE:
(define i (Date_inst_fiscal_year self ))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? i) (if (begin
	(Integer_inst_>= (let ([self self])(begin(define m (int (Date_inst_month (object-objectid self) )))(assume (and (Integer_inst_>= m (int 1) ) (Integer_inst_<= m (int 12) ) )) m)) (let ([tmp3 (Date_inst_fiscal_month_offset self )]) (begin (assume (not (stuck? tmp3))) tmp3)) )
	) (Integer_inst_== i (Integer_inst_+ (let ([self self])(begin(define y (int (Date_inst_year (object-objectid self) )))y)) (int 1) ) ) (void)))))

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
::BusinessTime::Config->9
|#
