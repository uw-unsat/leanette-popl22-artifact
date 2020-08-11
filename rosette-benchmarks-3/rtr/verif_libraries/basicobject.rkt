(define (obj-id-eq self other)
  (let ([id1 (object-objectid self)]
        [id2 (object-objectid other)])
    (return (= id1 id2))))
