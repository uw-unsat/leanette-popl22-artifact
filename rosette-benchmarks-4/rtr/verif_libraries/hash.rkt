(define (new_hash contents #:block [BLK (void)]) (let ([ret (object 0 (new-obj-id))]) (begin (set-object-contents! ret contents) (return ret))))

(define (Hash_inst_ref hsh key #:block [BLK (void)]) (let* ([contents (object-contents hsh)][value (findf (lambda (pair) (eq? (car pair) key)) contents)]) (if (eq? value #f) (return (void)) (return (cdr value)))))

(define (Hash_inst_each hsh #:block blk) (let ([contents (object-contents hsh)]) (begin (for-each (lambda (pair) (blk (car pair)(cdr pair))) contents) (return hsh))))

(define (Hash_inst_assign hsh k v #:block [BLK (void)]) (let* ([contents (object-contents hsh)][cont_no_k (remove k contents (lambda (k1 p) (eq? k1 (car p))))][new_cont (cons (cons k v) cont_no_k)]) (begin (set-object-contents! new_cont v) (return v))))

(define (Hash_inst_length hsh #:block [BLK (void)]) (return (length (object-contents hsh))))

