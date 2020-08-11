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
(struct object ([classid][objectid] [size #:auto #:mutable] [contents #:auto #:mutable] [vec #:auto #:mutable] [id #:auto #:mutable] [value #:auto #:mutable] [@hour #:auto #:mutable] [@min #:auto #:mutable] [@sec #:auto #:mutable] ) #:transparent #:auto-value (void))
 
;;; ARGUMENT DEFINITIONS:
  ; Initialize symbolic inputs to method 
  ; Initialize other of type BusinessTime::ParsedTime
(define other
(let ([other (object 6 (new-obj-id))])
(define @hour (begin (define-symbolic* @hour integer?) (int @hour)))

(define @min (begin (define-symbolic* @min integer?) (int @min)))

(define @sec (begin (define-symbolic* @sec integer?) (int @sec)))

(set-object-@hour! other @hour)
(set-object-@min! other @min)
(set-object-@sec! other @sec)
other))
  ; Initialize struct self of type BusinessTime::ParsedTime
(define self
(let ([self (object 6 (new-obj-id))])
(define @hour (begin (define-symbolic* @hour integer?) (int @hour)))

(define @min (begin (define-symbolic* @min integer?) (int @min)))

(define @sec (begin (define-symbolic* @sec integer?) (int @sec)))

(set-object-@hour! self @hour)
(set-object-@min! self @min)
(set-object-@sec! self @sec)
self))

;;; FUNCTION DEFINITIONS:
(define (BusinessTime::ParsedTime_inst_- self other #:block [BLK (void)])
	(let ()
	(return (Integer_inst_- (Integer_inst_+ (Integer_inst_+ (Integer_inst_* (begin
	(Integer_inst_- (let ([self self])(begin(define i (int (BusinessTime::ParsedTime_inst_hour (object-objectid self) )))(assume (Integer_inst_== i (object-@hour self) )) i)) (let ([self other])(begin(define i (int (BusinessTime::ParsedTime_inst_hour (object-objectid self) )))(assume (Integer_inst_== i (object-@hour self) )) i)) )
	) (int 3600) ) (Integer_inst_* (begin
	(Integer_inst_- (let ([self self])(begin(define j (int (BusinessTime::ParsedTime_inst_min (object-objectid self) )))(assume (Integer_inst_== j (object-@min self) )) j)) (let ([self other])(begin(define j (int (BusinessTime::ParsedTime_inst_min (object-objectid self) )))(assume (Integer_inst_== j (object-@min self) )) j)) )
	) (int 60) ) ) (let ([self self])(begin(define k (int (BusinessTime::ParsedTime_inst_sec (object-objectid self) )))(assume (Integer_inst_== k (object-@sec self) )) k)) ) (let ([self other])(begin(define k (int (BusinessTime::ParsedTime_inst_sec (object-objectid self) )))(assume (Integer_inst_== k (object-@sec self) )) k)) ))))

(define-symbolic BusinessTime::ParsedTime_inst_hour (~> integer? integer?))
(define-symbolic BusinessTime::ParsedTime_inst_min (~> integer? integer?))
(define-symbolic BusinessTime::ParsedTime_inst_sec (~> integer? integer?))
(define (BusinessTime::ParsedTime_inst_valid_time self t #:block [BLK (void)])
	(let ()
	(return (and (and (and (and (and (begin
	(Integer_inst_<= (int 0) (let ([self t])(begin(define i (int (BusinessTime::ParsedTime_inst_hour (object-objectid self) )))(assume (Integer_inst_== i (object-@hour self) )) i)) )
	) (begin
	(Integer_inst_< (let ([self t])(begin(define i (int (BusinessTime::ParsedTime_inst_hour (object-objectid self) )))(assume (Integer_inst_== i (object-@hour self) )) i)) (int 24) )
	) ) (begin
	(Integer_inst_<= (int 0) (let ([self t])(begin(define j (int (BusinessTime::ParsedTime_inst_min (object-objectid self) )))(assume (Integer_inst_== j (object-@min self) )) j)) )
	) ) (begin
	(Integer_inst_< (let ([self t])(begin(define j (int (BusinessTime::ParsedTime_inst_min (object-objectid self) )))(assume (Integer_inst_== j (object-@min self) )) j)) (int 60) )
	) ) (begin
	(Integer_inst_<= (int 0) (let ([self t])(begin(define k (int (BusinessTime::ParsedTime_inst_sec (object-objectid self) )))(assume (Integer_inst_== k (object-@sec self) )) k)) )
	) ) (begin
	(Integer_inst_< (let ([self t])(begin(define k (int (BusinessTime::ParsedTime_inst_sec (object-objectid self) )))(assume (Integer_inst_== k (object-@sec self) )) k)) (int 60) )
	) ))))

;;;RETURN VALUE:
(define diff (BusinessTime::ParsedTime_inst_- self other))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and (and (BusinessTime::ParsedTime_inst_valid_time self self ) (BusinessTime::ParsedTime_inst_valid_time self other ) ) )) #:guarantee (assert (unless (stuck? diff) (if (Integer_inst_> (let ([self self])(begin(define i (int (BusinessTime::ParsedTime_inst_hour (object-objectid self) )))(assume (Integer_inst_== i (object-@hour self) )) i)) (let ([self other])(begin(define i (int (BusinessTime::ParsedTime_inst_hour (object-objectid self) )))(assume (Integer_inst_== i (object-@hour self) )) i)) ) (Integer_inst_> diff (int 0) ) (void)))))

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
|#
