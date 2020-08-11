#lang rosette
(require "../../verif_libraries/ivl.rkt")

(require racket/include)(require racket/undefined)
(define USE_BV false)
(define BVSIZE 6)(include (file "../../verif_libraries/array.rkt"))
(include (file "../../verif_libraries/basicobject.rkt"))
(include (file "../../verif_libraries/bool.rkt"))
(include (file "../../verif_libraries/fixnum.rkt"))
(include (file "../../verif_libraries/float.rkt"))
(include (file "../../verif_libraries/hash.rkt"))
(include (file "../../verif_libraries/helper.rkt"))
(include (file "../../verif_libraries/ids.rkt"))
(include (file "../../verif_libraries/integer.rkt"))
(include (file "../../verif_libraries/kernel.rkt"))


;;; OBJECT STRUCT:
(struct object ([classid][objectid] [size #:auto #:mutable] [contents #:auto #:mutable] [vec #:auto #:mutable] [id #:auto #:mutable] [value #:auto #:mutable] ) #:transparent)
 
;;; ARGUMENT DEFINITIONS:
  ; Initialize f of type Folder
(define f
(let ([f (object 7 (new-obj-id))])
f))
  ; Initialize struct self of type UserFile
(define self
(let ([self (object 8 (new-obj-id))])
self))

;;; FUNCTION DEFINITIONS:
(define (UserFile_inst_move self target_folder #:block [BLK (void)])
	(let ()
	(begin
	(let ([self self][input target_folder])(begin  ; Initialize output of type Folder
(define output
(let ([output (object 7 (new-obj-id))])
output))(assume (obj-id-eq (let ([self self])(begin(define c (object 6 (UserFile_inst_folder (object-objectid self) )))c)) input )) output))
	(return (let ([self self])(begin  ; Initialize b of type false or true
(define-symbolic* b boolean?)
b)))
	)))

(define-symbolic UserFile_inst_folder (~> integer? integer?))
;;;RETURN VALUE:
(define b (UserFile_inst_move self f))

;;;VERIFIED ASSERTION:
(verify #:assume (assert (and )) #:guarantee (assert (unless (stuck? b) (obj-id-eq f (let ([self self])(begin(define c (UserFile_inst_folder (object-objectid self) )) c)) ))))


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
RDL::Verify->6
Folder->7
UserFile->8
|#
