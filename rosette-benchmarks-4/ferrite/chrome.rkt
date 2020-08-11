#lang rosette

(require "lib/fs.rkt" "lib/lang.rkt" "lib/litmus.rkt" 
         "lib/verifier.rkt" "lib/synth.rkt" "lib/ext4.rkt"
         rackunit)

(current-bitwidth 16)

(define small? #f)
(define writes (if small? '(33 2 31) '(2509 13 2500)))
(define block-size (if small? 64 4096))

(define chrome-setup 
  (list
   (creat 0)  ; fd 0
   (write 0 (for/list ([i (first writes)]) #t))
   (fsync 0)))

(define chrome-test
  (list
   (write 0 (for/list ([i (second writes)]) #t))
   (write 0 (for/list ([i (third writes)]) #t))))

; SeqFS
(define (chrome-allow oldfs newfs)
  ; file must be a prefix of #ts
  (define new-0 (ondisk newfs 0))
  (list (apply && new-0)))

; Ext4
(define (chrome-fs-ext4)
  (ext4-fs #:capacity 2 #:blocksize block-size))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (test-ext4)
  (printf "test-ext4 ~a\n" small?)
  (printf "  verify-correctness\n")
  (define test
    (litmus chrome-fs-ext4 chrome-setup chrome-test chrome-allow))
  (verify-correctness test)
  (void))

(time (test-ext4))