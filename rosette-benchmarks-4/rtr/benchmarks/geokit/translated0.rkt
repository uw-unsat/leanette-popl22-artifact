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
(struct object ([classid][objectid] [size #:auto #:mutable] [contents #:auto #:mutable] [vec #:auto #:mutable] [id #:auto #:mutable] [value #:auto #:mutable] [@sw #:auto #:mutable] [@ne #:auto #:mutable] ) #:transparent #:auto-value (void))
 
;;; ARGUMENT DEFINITIONS:
  ; Initialize symbolic inputs to method 
  ; Initialize struct self of type Geokit::Bounds
(define self
(let ([self (object 6 (new-obj-id))])
(define @sw
(let ([@sw (object 7 (new-obj-id))])
@sw))
(define @ne
(let ([@ne (object 7 (new-obj-id))])
@ne))
(set-object-@sw! self @sw)
(set-object-@ne! self @ne)
self))

;;; FUNCTION DEFINITIONS:
(define (Geokit::Bounds_inst_center self  #:block [BLK (void)])
	(let ()
	(return (let ([self (object-@sw self)][g (object-@ne self)])(begin(define m (int (Geokit::LatLng_inst_midpoint_to (object-objectid self) (object-objectid g))))m)))))

(define-symbolic Geokit::LatLng_inst_midpoint_to (~> integer? integer? integer?))
;;;RETURN VALUE:
(define j (Geokit::Bounds_inst_center self ))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? j) (Integer_inst_== j (let ([self (object-@sw self)][g (object-@ne self)])(begin(define m (int (Geokit::LatLng_inst_midpoint_to (object-objectid self) (object-objectid g))))m)) ))))

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
|#
