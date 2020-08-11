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
(struct object ([classid][objectid] [size #:auto #:mutable] [contents #:auto #:mutable] [vec #:auto #:mutable] [id #:auto #:mutable] [value #:auto #:mutable] [@sw #:auto #:mutable] [@ne #:auto #:mutable] [@lng #:auto #:mutable] [@lat #:auto #:mutable] [@points #:auto #:mutable] ) #:transparent #:auto-value (void))
 
;;; ARGUMENT DEFINITIONS:
  ; Initialize symbolic inputs to method 
  ; Initialize point of type Geokit::LatLng
(define point
(let ([point (object 7 (new-obj-id))])
(define @lng (begin (define-symbolic* @lng integer?) (int @lng)))

(define @lat (begin (define-symbolic* @lat integer?) (int @lat)))

(set-object-@lng! point @lng)
(set-object-@lat! point @lat)
point))
  ; Initialize struct self of type Geokit::Polygon
(define self
(let ([self (object 11 (new-obj-id))])
(define @points
(new-symbolic-array
(lambda (__IDX)
(define __CONSTRUCTED_ELE
(let ([__CONSTRUCTED_ELE (object 7 (new-obj-id))])
(define @lng (begin (define-symbolic* @lng integer?) (int @lng)))

(define @lat (begin (define-symbolic* @lat integer?) (int @lat)))

(set-object-@lng! __CONSTRUCTED_ELE @lng)
(set-object-@lat! __CONSTRUCTED_ELE @lat)
__CONSTRUCTED_ELE))
(return __CONSTRUCTED_ELE))))
(set-object-@points! self @points)
self))

;;; FUNCTION DEFINITIONS:
(define (Geokit::Polygon_inst_contains? self point #:block [BLK (void)])
	(let ([last_point 'undefined][oddNodes 'undefined][x 'undefined][y 'undefined][yi 'undefined][xi 'undefined][yj 'undefined][xj 'undefined])
	(begin
	
	
	
	
	(begin (set! last_point (Array_inst_ref (object-@points self) (int -1) ))  last_point)
	(begin (set! oddNodes false)  oddNodes)
	(begin (set! x (let ([self point])(begin(define i (int (Geokit::LatLng_inst_lng (object-objectid self) )))(assume (Integer_inst_== i (object-@lng self) )) i)))  x)
	(begin (set! y (let ([self point])(begin(define i (int (Geokit::LatLng_inst_lat (object-objectid self) )))(assume (Integer_inst_== i (object-@lat self) )) i)))  y)
	(Array_inst_each (object-@points self) #:block (lambda (p)
(begin
	(begin (set! yi (let ([self p])(begin(define i (int (Geokit::LatLng_inst_lat (object-objectid self) )))(assume (Integer_inst_== i (object-@lat self) )) i)))  yi)
	(begin (set! xi (let ([self p])(begin(define i (int (Geokit::LatLng_inst_lng (object-objectid self) )))(assume (Integer_inst_== i (object-@lng self) )) i)))  xi)
	(begin (set! yj (let ([self last_point])(begin(define i (int (Geokit::LatLng_inst_lat (object-objectid self) )))(assume (Integer_inst_== i (object-@lat self) )) i)))  yj)
	(begin (set! xj (let ([self last_point])(begin(define i (int (Geokit::LatLng_inst_lng (object-objectid self) )))(assume (Integer_inst_== i (object-@lng self) )) i)))  xj)
	(if (or (and (Integer_inst_< yi y ) (Integer_inst_>= yj y ) ) (and (Integer_inst_< yj y ) (Integer_inst_>= yi y ) ) ) (if (Integer_inst_< (Integer_inst_+ xi (Integer_inst_* (Integer_inst_/ (begin
	(Integer_inst_- y yi )
	) (begin
	(Integer_inst_- yj yi )
	) ) (begin
	(Integer_inst_- xj xi )
	) ) ) x ) (begin (set! oddNodes (! oddNodes ))  oddNodes) (void)) (void))
	(begin (set! last_point p)  (return last_point))
	)))
	(return oddNodes)
	)))

(define-symbolic Geokit::LatLng_inst_lng (~> integer? integer?))
(define-symbolic Geokit::LatLng_inst_lat (~> integer? integer?))
;;;RETURN VALUE:
(define b (Geokit::Polygon_inst_contains? self point))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? b) (if (Integer_inst_<= (Array_inst_size (object-@points self) ) (int 1) ) (eq? b false ) (void)))))

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
Geokit::GeoLoc->10
Geokit::Polygon->11
|#
