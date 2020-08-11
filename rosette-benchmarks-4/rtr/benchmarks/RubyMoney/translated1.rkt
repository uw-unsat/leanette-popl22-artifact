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
  ; Initialize m of type Money::Arithmetic
(define m
(let () (define-symbolic* classid integer?) (let ([m (object classid (new-obj-id))])
m))
)
  ; Initialize struct self of type Money::Arithmetic
(define self
(let () (define-symbolic* classid integer?) (let ([self (object classid (new-obj-id))])
self))
)

;;; FUNCTION DEFINITIONS:
(define (Money::Arithmetic_inst_eql? self other_money #:block [BLK (void)])
	(let ()
	(if (Kernel_inst_is_a? other_money (let ([tmp (object 1 7)]) (begin (set-object-id! tmp 7) tmp)) ) (return (or (begin
	(and (Integer_inst_== (let ([self self])(begin(define tmpname5 (int (Money::Arithmetic_inst_fractional (object-objectid self) )))tmpname5)) (let ([self other_money])(begin(define tmpname6 (int (Money::Arithmetic_inst_fractional (object-objectid self) )))tmpname6)) ) (Integer_inst_== (let ([self self])(begin  ; Initialize tmpname7 of type Bignum or Fixnum
(define tmpname7 (begin (define-symbolic* tmpname7 integer?) (int tmpname7)))
tmpname7)) (let ([self other_money])(begin  ; Initialize tmpname8 of type Bignum or Fixnum
(define tmpname8 (begin (define-symbolic* tmpname8 integer?) (int tmpname8)))
tmpname8)) ) )
	) (begin
	(and (Integer_inst_== (let ([self self])(begin(define tmpname9 (int (Money::Arithmetic_inst_fractional (object-objectid self) )))tmpname9)) (int 0) ) (Integer_inst_== (let ([self other_money])(begin(define tmpname10 (int (Money::Arithmetic_inst_fractional (object-objectid self) )))tmpname10)) (int 0) ) )
	) )) (return false))))

(define-symbolic Money::Arithmetic_inst_fractional (~> integer? integer?))
;;;RETURN VALUE:
(define b (Money::Arithmetic_inst_eql? self m))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? b) (if (and (and (Kernel_inst_is_a? m (let ([tmp (object 1 7)]) (begin (set-object-id! tmp 7) tmp)) ) (begin
	(Integer_inst_== (let ([self m])(begin(define tmpname11 (int (Money::Arithmetic_inst_fractional (object-objectid self) )))tmpname11)) (int 0) )
	) ) (begin
	(Integer_inst_== (let ([self self])(begin(define tmpname12 (int (Money::Arithmetic_inst_fractional (object-objectid self) )))tmpname12)) (int 0) )
	) ) b (void)))))

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
