(define CLASSID 1)

(define (Kernel_inst_is_a? self kl)

  (let ([kl_id (object-id kl)])
    (cond [(integer? self) (return (= kl_id 3))]
          [(real? self) (return (= kl_id 4))]
          [else (return (= (object-classid self) kl_id))]))) ;; TODO: account for superclasses?

(define (Kernel_inst_class self) (let ([self_id (object-classid self)][kl (object CLASSID (new-obj-id))]) (begin (set-object-id! kl self_id) (return kl))))
(define (Kernel_class self) (let ([self_id (object-classid self)][kl (object CLASSID (new-obj-id))]) (begin (set-object-id! kl self_id) (return kl))))

(define (Kernel_inst_nil? self) (return (void? self)))
