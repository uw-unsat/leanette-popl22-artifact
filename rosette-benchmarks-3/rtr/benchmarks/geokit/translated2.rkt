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
(struct object ([classid][objectid] [size #:auto #:mutable] [contents #:auto #:mutable] [vec #:auto #:mutable] [id #:auto #:mutable] [value #:auto #:mutable] [@sw #:auto #:mutable] [@ne #:auto #:mutable] [@lng #:auto #:mutable] ) #:transparent #:auto-value (void))
 
;;; ARGUMENT DEFINITIONS:
  ; Initialize symbolic inputs to method 
  ; Initialize other of type Geokit::Bounds
(define other
(let ([other (object 6 (new-obj-id))])
(define @sw
(let ([@sw (object 7 (new-obj-id))])
(define @lng (begin (define-symbolic* @lng integer?) (int @lng)))

(set-object-@lng! @sw @lng)
@sw))
(define @ne
(let ([@ne (object 7 (new-obj-id))])
(define @lng (begin (define-symbolic* @lng integer?) (int @lng)))

(set-object-@lng! @ne @lng)
@ne))
(set-object-@sw! other @sw)
(set-object-@ne! other @ne)
other))
  ; Initialize struct self of type Geokit::Bounds
(define self
(let ([self (object 6 (new-obj-id))])
(define @sw
(let ([@sw (object 7 (new-obj-id))])
(define @lng (begin (define-symbolic* @lng integer?) (int @lng)))

(set-object-@lng! @sw @lng)
@sw))
(define @ne
(let ([@ne (object 7 (new-obj-id))])
(define @lng (begin (define-symbolic* @lng integer?) (int @lng)))

(set-object-@lng! @ne @lng)
@ne))
(set-object-@sw! self @sw)
(set-object-@ne! self @ne)
self))

;;; FUNCTION DEFINITIONS:
(define (Geokit::Bounds_inst_== self other #:block [BLK (void)])
	(let ()
	(begin
	(if (Kernel_inst_is_a? other (let ([tmp (object 1 8)]) (begin (set-object-id! tmp 8) tmp)) ) (void) (return false))
	(return (and (equal? (let ([self self])(begin(define g (object 9 (Geokit::Bounds_inst_sw (object-objectid self) )))(assume (equal? g (object-@sw self) )) g)) (let ([self other])(begin(define g (object 9 (Geokit::Bounds_inst_sw (object-objectid self) )))(assume (equal? g (object-@sw self) )) g)) ) (equal? (let ([self self])(begin(define g (object 9 (Geokit::Bounds_inst_ne (object-objectid self) )))(assume (equal? g (object-@ne self) )) g)) (let ([self other])(begin(define g (object 9 (Geokit::Bounds_inst_ne (object-objectid self) )))(assume (equal? g (object-@ne self) )) g)) ) ))
	)))

(define-symbolic Geokit::Bounds_inst_sw (~> integer? integer?))
(define-symbolic Geokit::Bounds_inst_ne (~> integer? integer?))
;;;RETURN VALUE:
(define b (Geokit::Bounds_inst_== self other))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? b) (if b (and (and (Kernel_inst_is_a? other (let ([tmp (object 1 8)]) (begin (set-object-id! tmp 8) tmp)) ) (begin
	(equal? (let ([self self])(begin(define g (object 9 (Geokit::Bounds_inst_sw (object-objectid self) )))(assume (equal? g (object-@sw self) )) g)) (let ([self other])(begin(define g (object 9 (Geokit::Bounds_inst_sw (object-objectid self) )))(assume (equal? g (object-@sw self) )) g)) )
	) ) (begin
	(equal? (let ([self self])(begin(define g (object 9 (Geokit::Bounds_inst_ne (object-objectid self) )))(assume (equal? g (object-@ne self) )) g)) (let ([self other])(begin(define g (object 9 (Geokit::Bounds_inst_ne (object-objectid self) )))(assume (equal? g (object-@ne self) )) g)) )
	) ) (void)))))

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
Geokit::Bounds->6
Geokit::LatLng->7
::Geokit::Bounds->8
RDL::Verify->9
|#
