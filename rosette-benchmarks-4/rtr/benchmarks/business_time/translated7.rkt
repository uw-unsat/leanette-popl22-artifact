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
(define (Date_inst_fiscal_year_month self  #:block [BLK (void)])
	(let ([shifted_month 'undefined])
	(begin
	(begin (set! shifted_month (Integer_inst_- (let ([self self])(begin(define m (int (Date_inst_month (object-objectid self) )))(assume (and (Integer_inst_>= m (int 1) ) (Integer_inst_<= m (int 12) ) )) m)) (begin
	(Integer_inst_- (let ([tmp0 (Date_inst_fiscal_month_offset self )]) (begin (assume (not (stuck? tmp0))) tmp0)) (int 1) )
	) ))  shifted_month)
	(if (Integer_inst_<= shifted_month (int 0) ) (begin (set! shifted_month (Integer_inst_+ shifted_month (int 12) ))  shifted_month) (void))
	(return shifted_month)
	)))

(define-symbolic Date_inst_month (~> integer? integer?))
(define (Date_inst_fiscal_month_offset self  #:block [BLK (void)])
	(let ()
	(return (let ([self (let ([tmp (object 1 9)]) (begin (set-object-id! tmp 9) tmp))])(begin(define fm (int (BusinessTime::Config_inst_fiscal_month_offset (object-objectid self) )))(assume (and (Integer_inst_>= fm (int 1) ) (Integer_inst_<= fm (int 12) ) )) fm)))))
(define-symbolic BusinessTime::Config_inst_fiscal_month_offset (~> integer? integer?))
;;;RETURN VALUE:
(define fym (Date_inst_fiscal_year_month self ))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? fym) (and (Integer_inst_>= fym (int 1) ) (Integer_inst_<= fym (int 12) ) ))))

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
