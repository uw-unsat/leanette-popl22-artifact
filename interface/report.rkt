#lang racket

(require text-table
         csv-reading)

(define data-3 (csv->list (open-input-file "workspace/rosette-3-total.csv")))
(define data-4 (csv->list (open-input-file "workspace/rosette-4-total.csv")))
(define data-diff (csv->list (open-input-file "workspace/diff.csv")))

(define r3 (for/hash ([row data-3]) (values (first row) (second row))))
(define r4 (for/hash ([row data-4]) (values (first row) (second row))))
(define rdiff (for/hash ([row data-diff]) (values (first row) (rest row))))

(define all-names (sort (set-remove (map first data-3) "jitterbug") string<?))

(define (add-comma n)
  (define s (if (string? n)
                n
                (number->string n)))
  (string-append*
   (reverse
    (for/list ([digit (reverse (string->list s))] [i (in-naturals)])
      (cond
        [(zero? i) (string digit)]
        [(zero? (modulo i 3)) (string digit #\,)]
        [else (string digit)])))))

(define replacement (hash "Greenthumb" "GreenThumb~\\cite{phothilimthana:greenthumb}"
                          "Ifcl" "IFCL~\\cite{rosette:pldi}"
                          "Memsynth" "MemSynth~\\cite{memsynth}"
                          "Rtr" "RTR~\\cite{kazerounian:rtr}"
                          "Synthcl" "SynthCL~\\cite{rosette:pldi}"
                          "Websynth" "WebSynth~\\cite{rosette:pldi}"

                          "Bagpipe" "Bagpipe~\\cite{weitz:bagpipe}"
                          "Bonsai" "Bonsai~\\cite{chandra:bonsai}"
                          "Cosette" "Cosette~\\cite{chu:cosette}"
                          "Ferrite" "Ferrite~\\cite{ferrite}"
                          "Fluidics" "Fluidics~\\cite{willsey:puddle}"
                          "Neutrons" "Neutrons~\\cite{pernsteiner:neutrons}"
                          "Nonograms" "Nonograms~\\cite{butler:nonograms}"
                          "Quivela" "Quivela~\\cite{aws:quivela}"
                          "Wallingford" "Wallingford~\\cite{borning:wallingford}"

                          "Jitterbug" "Jitterbug~\\cite{jitterbug}"))

(print-table
 (cons
  (list "Benchmark" "Rosette LoC" "Rosette* LoC" "LoC diff" "" "Solver")
  (for/list ([name (in-sequences all-names (list "jitterbug"))])
    (define loc-3 (string->number (hash-ref r3 name)))
    (define loc-4 (string->number (hash-ref r4 name)))
    (define loc-diff (map string->number (hash-ref rdiff name)))
    (define name* (string-titlecase name))

    (unless (= (- (first loc-diff) (second loc-diff)) (- loc-4 loc-3))
      (println (list 'mismatch name loc-3 loc-4 loc-diff)))

    (list (hash-ref replacement name* name*)
          (add-comma loc-3)
          (add-comma loc-4)
          (format "+~a" (add-comma (first loc-diff)))
          (format "-~a" (add-comma (second loc-diff)))
          (third (hash-ref rdiff name))))))
